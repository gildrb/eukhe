# eukhe: the laws of area optchat

import Base
import ../bend/compactor.bend as C
import ../bend/ffi_optchat.bend as FOc
import ../bend/optchat/bits.bend as OBits
import ../bend/optchat/ctx.bend as OCtx
import ../bend/optchat/fit.bend as OFit
import ../bend/optchat/info.bend as OInfo
import ../bend/optchat/node.bend as ONode
import ../bend/optchat/push.bend as OPush
import ../bend/optchat/queue.bend as OQueue
import ../bend/optchat/state.bend as OState
import ../bend/optchat/step.bend as OStep
import ../bend/spec.bend as S
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# (a) The view
# ------------

# LAW view_covers: after any history, the view covers messages 0..T-1 exactly once,
# contiguous, oldest first, every line an aligned tree node (gist §3)
law view_covers:
  for +cfg: OState.Cfg
  for +evs: List<&2, OState.Ev>
  S.Tiles(0n, S.view.of(cfg, evs), S.total.of(cfg, evs))

# LAW cview_covers: so does the compaction view (gist §4)
law cview_covers:
  for +cfg: OState.Cfg
  for +evs: List<&2, OState.Ev>
  S.Tiles(0n, S.cview.of(cfg, evs), S.total.of(cfg, evs))

# (b) A message
# -------------

# LAW message_appends: when no batch runs, a message only appends its own line: the
# old view is a prefix of the new one (gist §3.2, §3.3)
law message_appends:
  for +cfg: OState.Cfg
  for +s: OState.St
  for quiet: {OStep.St.batch(cfg, s) == False{} : Bool}
  {OState.St.view(Pair.fst(OState.St, List<&2, ONode.Node>, OStep.msg(cfg, s))) == List.append(&2, ONode.Node, OState.St.view(s), [ONode.Node.leaf(OState.St.t(s))]) : List<&2, ONode.Node>}

# LAW message_merges_nothing: and it merges nothing
law message_merges_nothing:
  for +cfg: OState.Cfg
  for +s: OState.St
  for quiet: {OStep.St.batch(cfg, s) == False{} : Bool}
  {Pair.snd(OState.St, List<&2, ONode.Node>, OStep.msg(cfg, s)) == Nil{} : List<&2, ONode.Node>}

# (c) A merge
# -----------

# LAW merge_is_one_pair: a merge replaces two sibling lines by their built parent, or
# changes nothing (gist §3.1)
law merge_is_one_pair:
  for +info: OInfo.Info
  for +v: List<&2, ONode.Node>
  for +a: ONode.Node
  Or({OFit.merge(info, v, a) == v : List<&2, ONode.Node>}, S.Merged(info, v, OFit.merge(info, v, a)))

# LAW merge_covers: a merge keeps the coverage
law merge_covers:
  for +info: OInfo.Info
  for +s: Nat
  for +v: List<&2, ONode.Node>
  for +w: List<&2, ONode.Node>
  for +e: Nat
  for tiles: S.Tiles(s, v, e)
  for merged: S.Merged(info, v, w)
  S.Tiles(s, w, e)

# (d) Taelin's push
# -----------------

# LAW push_agrees: with push's list length as the budget (a line counts 1 byte,
# every node built), the due order (T - last) / 2^l makes exactly the
# merges of Taelin's rollback push, at every step t = 0..20,000 (gist
# §3.2: "checked for t = 0..20,000"). Bounded: proven by computation.
law push_agrees:
  {OPush.agree(OFit.Last{}, 20001n) == True{} : Bool}

# LAW push_agrees_always: and at every step t of any number n of pushes: after each push the
# view and push's list hold the same lines (gist §3.2, for all t)
law push_agrees_always:
  for n: Nat
  {OPush.agree(OFit.Last{}, n) == True{} : Bool}

# (e) A batch
# -----------

# LAW fit_reaches_budget: a fit ends at most at its budget, unless no pair can merge (every
# remaining pair's parent is unbuilt) (gist §3.2)
law fit_reaches_budget:
  for +m: OFit.Age
  for +t: List<&2, Bool>
  for +budget: Nat
  for +ph: Nat
  for +info: OInfo.Info
  for +v: List<&2, ONode.Node>
  Or({Nat.is_le(OFit.view_size(ph, info, OFit.fit.view(m, t, budget, ph, info, v)), budget) == True{} : Bool}, {S.can_merge(info, OFit.fit.view(m, t, budget, ph, info, v)) == False{} : Bool})

# LAW fit_merges_built: a fit merges only into built parents
law fit_merges_built:
  for +m: OFit.Age
  for +t: List<&2, Bool>
  for +budget: Nat
  for +ph: Nat
  for +info: OInfo.Info
  for +v: List<&2, ONode.Node>
  S.Built(info, Pair.fst(List<&2, ONode.Node>, List<&2, ONode.Node>, OFit.fit(m, t, budget, ph, info, v)))

# LAW view_summarized: after any history, every merged line of the view is built: only
# a message's own line may still wait for its summary (gist §3)
law view_summarized:
  for +cfg: OState.Cfg
  for +evs: List<&2, OState.Ev>
  S.Summarized(OState.St.info(OStep.run(cfg, evs)), S.view.of(cfg, evs))

# LAW cview_summarized: so is every merged line of the compaction view
law cview_summarized:
  for +cfg: OState.Cfg
  for +evs: List<&2, OState.Ev>
  S.Summarized(OState.St.info(OStep.run(cfg, evs)), S.cview.of(cfg, evs))

# (f) First is not last
# ---------------------
# At T = 10, with the view 0+4, 4+4, 8+1, 9+1 and a budget of 3 lines
# (gist §3.2):

# LAW last_merges_8_9: due from the pair's last message merges 8-9, as push does
law last_merges_8_9:
  {OFit.fit.view(OFit.Last{}, S.ten(), 3n, 0n, OInfo.All{1n}, S.view10()) == [ONode.Node{2n, []}, ONode.Node{2n, [True{}]}, ONode.Node{1n, [False{}, False{}, True{}]}] : List<&2, ONode.Node>}

# LAW first_merges_0_7: due from its first message merges 0-7 instead
law first_merges_0_7:
  {OFit.fit.view(OFit.First{}, S.ten(), 3n, 0n, OInfo.All{1n}, S.view10()) == [ONode.Node{3n, []}, ONode.Node{0n, [False{}, False{}, False{}, True{}]}, ONode.Node{0n, [True{}, False{}, False{}, True{}]}] : List<&2, ONode.Node>}

# LAW first_is_not_last: so the two measures are not the same
law first_is_not_last:
  {OFit.fit.view(OFit.First{}, S.ten(), 3n, 0n, OInfo.All{1n}, S.view10()) != OFit.fit.view(OFit.Last{}, S.ten(), 3n, 0n, OInfo.All{1n}, S.view10()) : List<&2, ONode.Node>}

# LAW first_leaves_push: and from the first message the view leaves push within 11 steps
law first_leaves_push:
  {OPush.agree(OFit.First{}, 11n) == False{} : Bool}

# (g) A compaction's view
# -----------------------

# LAW context_ends_at_node: a compaction's view ends at its node (before the message, or by
# the merge's last message) and holds only built lines (gist §4)
law context_ends_at_node:
  for +s: OState.St
  for +n: ONode.Node
  S.Before(OState.St.info(s), OCtx.ctx.bound(n), OCtx.ctx(s, n))

# LAW context_is_prefix: it is the start of the compaction view, so compactions share
# their cache prefix (gist §4)
law context_is_prefix:
  for +s: OState.St
  for +n: ONode.Node
  S.Prefix(OCtx.ctx(s, n), OState.St.cview(s))

# (H2) A turn never waits forever for the memory
# ----------------------------------------------
# docs/harness.md H2: the need-first queue of bend/optchat/queue.bend, the settle
# of bend/compactor.bend.

# LAW need_progress: the queue never stalls a waiting turn: after any events, while
# fewer than jobs calls run and a view line is neither built nor busy,
# the queue starts a node
law need_progress:
  for +cfg: OState.Cfg
  for +evs: List<&2, OState.Ev>
  for room: {Nat.is_lt(List.length(&2, ONode.Node, OState.St.busy(OStep.run(cfg, evs))), OState.Cfg.jobs(cfg)) == True{} : Bool}
  for idle: {C.idle(OState.St.info(OStep.run(cfg, evs)), OState.St.view(OStep.run(cfg, evs)), OState.St.busy(OStep.run(cfg, evs))) == True{} : Bool}
  {OBits.Nat.is_pos(List.length(&2, ONode.Node, OQueue.cands.need(cfg, OStep.run(cfg, evs)))) == True{} : Bool}

# (S) The planner runs as a stepper of the compiled core
# ------------------------------------------------------
# docs/memory.md. The chat (crates/eukhe-core/src/memory/chat.rs) opens
# the stepper bend/ffi_optchat.bend from its loaded log, sends each event
# as it happens (a message, a node built, a call started or freed, a turn
# that starts to wait) and each query it needs (the nodes to start, with
# or without a waiting turn, a compaction's view, how many calls run), and
# does what each reply says. It keeps the texts; it decides nothing. Every
# law holds for every order of events: the events are free.

# Spellers: the bytes the chat sends and reads, from the wire's primitives

# a node on the wire: its level, then its index
def oc_spell_node(n: ONode.Node, rest: String) -> String:
  match n:
    case ONode.Node{l, i}:
      Wr.put_nat(l, Wr.put_nat(OBits.Bits.val(i), rest))

def oc_spell_nodes.items(ns: List<&2, ONode.Node>, rest: String) -> String:
  match ns:
    case Nil{}:
      rest
    case n <> t:
      oc_spell_node(n, oc_spell_nodes.items(t, rest))

# nodes: their count, then each node
def oc_spell_nodes(+ns: List<&2, ONode.Node>, rest: String) -> String:
  Wr.put_nat(List.length(&2, ONode.Node, ns), oc_spell_nodes.items(ns, rest))

# a level and an index, then rest
def oc_spell_lk(l: Nat, k: Nat, rest: String) -> String:
  Wr.put_nat(l, Wr.put_nat(k, rest))

# an event or a query as the chat writes it: 0 a message; 1 a node built
# (l, k, size); 2 its call started (l, k); 3 its call freed (l, k); 4 a
# turn starts to wait; 5 the nodes to start; 6 the nodes to start while a
# turn waits; 7 a compaction's view of a node (l, k); 8 how many calls run
def oc_spell(q: FOc.Q) -> String:
  match q:
    case FOc.QMsg{}:
      Wr.put_nat(0n, "")
    case FOc.QBuilt{l, k, z}:
      Wr.put_nat(1n, oc_spell_lk(l, k, Wr.put_nat(z, "")))
    case FOc.QStart{l, k}:
      Wr.put_nat(2n, oc_spell_lk(l, k, ""))
    case FOc.QFree{l, k}:
      Wr.put_nat(3n, oc_spell_lk(l, k, ""))
    case FOc.QWait{}:
      Wr.put_nat(4n, "")
    case FOc.QCands{}:
      Wr.put_nat(5n, "")
    case FOc.QNeed{}:
      Wr.put_nat(6n, "")
    case FOc.QCtx{l, k}:
      Wr.put_nat(7n, oc_spell_lk(l, k, ""))
    case FOc.QBusy{}:
      Wr.put_nat(8n, "")

# every number of q fits the wire
def oc_fits(q: FOc.Q) -> Bool:
  match q:
    case FOc.QMsg{}:
      True{}
    case FOc.QBuilt{l, k, z}:
      Bool.and(LawsBase.wire_fits(l), Bool.and(LawsBase.wire_fits(k), LawsBase.wire_fits(z)))
    case FOc.QStart{l, k}:
      Bool.and(LawsBase.wire_fits(l), LawsBase.wire_fits(k))
    case FOc.QFree{l, k}:
      Bool.and(LawsBase.wire_fits(l), LawsBase.wire_fits(k))
    case FOc.QWait{}:
      True{}
    case FOc.QCands{}:
      True{}
    case FOc.QNeed{}:
      True{}
    case FOc.QCtx{l, k}:
      Bool.and(LawsBase.wire_fits(l), LawsBase.wire_fits(k))
    case FOc.QBusy{}:
      True{}

def oc_spell_gots.items(bs: List<&2, FOc.Got>, rest: String) -> String:
  match bs:
    case Nil{}:
      rest
    case FOc.Got{l, k, z} <> t:
      oc_spell_lk(l, k, Wr.put_nat(z, oc_spell_gots.items(t, rest)))

def oc_spell_lines.items(vs: List<&2, FOc.Line>, rest: String) -> String:
  match vs:
    case Nil{}:
      rest
    case FOc.Line{l, k} <> t:
      oc_spell_lk(l, k, oc_spell_lines.items(t, rest))

# the open as the chat writes it: the sizes (ph, ceil, floor, cceil,
# cfloor, jobs), T, the built nodes (count, then l, k, size each), the
# view (count, then l, k each), shrink, missed
def oc_spell_open(o: FOc.Open) -> String:
  match o:
    case FOc.Open{c, t, +bs, +vs, sh, m}:
      match c:
        case OState.Cfg{ph, ce, fl, cc, cf, j}:
          Wr.put_nat(ph, Wr.put_nat(ce, Wr.put_nat(fl, Wr.put_nat(cc, Wr.put_nat(cf, Wr.put_nat(j, Wr.put_nat(t, Wr.put_nat(List.length(&2, FOc.Got, bs), oc_spell_gots.items(bs, Wr.put_nat(List.length(&2, FOc.Line, vs), oc_spell_lines.items(vs, Wr.put_bool(sh, Wr.put_bool(m, "")))))))))))))

def oc_gots_fit(bs: List<&2, FOc.Got>) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case FOc.Got{l, k, z} <> t:
      Bool.and(LawsBase.wire_fits(l), Bool.and(LawsBase.wire_fits(k), Bool.and(LawsBase.wire_fits(z), oc_gots_fit(t))))

def oc_lines_fit(vs: List<&2, FOc.Line>) -> Bool:
  match vs:
    case Nil{}:
      True{}
    case FOc.Line{l, k} <> t:
      Bool.and(LawsBase.wire_fits(l), Bool.and(LawsBase.wire_fits(k), oc_lines_fit(t)))

# every number of the open fits the wire
def oc_open_fits(o: FOc.Open) -> Bool:
  match o:
    case FOc.Open{c, t, +bs, +vs, sh, m}:
      match c:
        case OState.Cfg{ph, ce, fl, cc, cf, j}:
          Bool.and(LawsBase.wire_nats_fit([ph, ce, fl, cc, cf, j, t, List.length(&2, FOc.Got, bs), List.length(&2, FOc.Line, vs)]), Bool.and(oc_gots_fit(bs), oc_lines_fit(vs)))

def oc_state(r: FOc.St & String) -> FOc.St:
  (s, x) = r
  s

def oc_reply_of(r: FOc.St & String) -> String:
  (s, x) = r
  x

# What the model asks

# the node a level and an index name: the index k in binary, the model's
# bits (law optchat_bits_of pins them)
def oc_node(l: Nat, k: Nat) -> ONode.Node:
  ONode.Node{l, OBits.Bits.of(k)}

# the busy nodes a waiting turn stops: those that are not view lines
# still unbuilt (docs/harness.md H2.1)
def oc_held.pick(stop: Bool, +b: ONode.Node, rest: List<&2, ONode.Node>) -> List<&2, ONode.Node>:
  match stop:
    case True{}:
      b <> rest
    case False{}:
      rest

def oc_held(+info: OInfo.Info, +v: List<&2, ONode.Node>, bs: List<&2, ONode.Node>) -> List<&2, ONode.Node>:
  match bs:
    case Nil{}:
      Nil{}
    case +b <> rest:
      oc_held.pick(Bool.not(Bool.and(ONode.Nodes.has(v, b), Bool.not(OInfo.Info.built(info, b)))), b, oc_held(info, v, rest))

# a batch, spelled: 0 none ran; 1 one ran: its merged nodes in merge
# order, the view after it, and whether it is still over its floor
def oc_spell_batch(ran: Bool, merged: List<&2, ONode.Node>, +s: OState.St) -> String:
  match ran:
    case False{}:
      Wr.put_nat(0n, "")
    case True{}:
      Wr.put_nat(1n, oc_spell_nodes(merged, oc_spell_nodes(OState.St.view(s), Wr.put_bool(OState.St.shrink(s), ""))))

# the chat after q, as the model moves it: a message, a build, a start, a
# free are the model's events; a wait stops the calls the turn does not
# need; a query moves nothing
def oc_next(+cfg: OState.Cfg, +s: OState.St, q: FOc.Q) -> OState.St:
  match q:
    case FOc.QMsg{}:
      Pair.fst(OState.St, List<&2, ONode.Node>, OStep.step(cfg, s, OState.Msg{}))
    case FOc.QBuilt{l, k, z}:
      Pair.fst(OState.St, List<&2, ONode.Node>, OStep.step(cfg, s, OState.Build{oc_node(l, k), z}))
    case FOc.QStart{l, k}:
      Pair.fst(OState.St, List<&2, ONode.Node>, OStep.step(cfg, s, OState.Start{oc_node(l, k)}))
    case FOc.QFree{l, k}:
      Pair.fst(OState.St, List<&2, ONode.Node>, OStep.step(cfg, s, OState.Free{oc_node(l, k)}))
    case FOc.QWait{}:
      OQueue.St.wait(s)
    case FOc.QCands{}:
      s
    case FOc.QNeed{}:
      s
    case FOc.QCtx{l, k}:
      s
    case FOc.QBusy{}:
      s

# the reply to q, as the model answers it: a message answers the batch it
# ran (OStep.St.batch decides whether one runs, OStep.step makes it); a
# build, a start, a free answer done (0); a wait answers the calls it
# stops; the queries answer cands, cands.need, ctx and the busy count
def oc_reply(+cfg: OState.Cfg, +s: OState.St, q: FOc.Q) -> String:
  match q:
    case FOc.QMsg{}:
      oc_spell_batch(OStep.St.batch(cfg, s), Pair.snd(OState.St, List<&2, ONode.Node>, OStep.step(cfg, s, OState.Msg{})), Pair.fst(OState.St, List<&2, ONode.Node>, OStep.step(cfg, s, OState.Msg{})))
    case FOc.QBuilt{l, k, z}:
      Wr.put_nat(0n, "")
    case FOc.QStart{l, k}:
      Wr.put_nat(0n, "")
    case FOc.QFree{l, k}:
      Wr.put_nat(0n, "")
    case FOc.QWait{}:
      oc_spell_nodes(oc_held(OState.St.info(s), OState.St.view(s), OState.St.busy(s)), "")
    case FOc.QCands{}:
      oc_spell_nodes(OQueue.cands(cfg, s), "")
    case FOc.QNeed{}:
      oc_spell_nodes(OQueue.cands.need(cfg, s), "")
    case FOc.QCtx{l, k}:
      oc_spell_nodes(OCtx.ctx(s, oc_node(l, k)), "")
    case FOc.QBusy{}:
      Wr.put_nat(List.length(&2, ONode.Node, OState.St.busy(s)), "")

# The open, as the model asks it

# every built node's size (a later copy of a node wins)
def oc_info(bs: List<&2, FOc.Got>, info: OInfo.Info) -> OInfo.Info:
  match bs:
    case Nil{}:
      info
    case FOc.Got{l, k, z} <> rest:
      oc_info(rest, OInfo.Info.set(info, oc_node(l, k), z))

# the ready merges: each built node noted as a build notes it
# (OStep.ready.note: its parent, once both halves are built and the parent
# is not)
def oc_ready(bs: List<&2, FOc.Got>, +info: OInfo.Info, rs: List<&2, ONode.Node>) -> List<&2, ONode.Node>:
  match bs:
    case Nil{}:
      rs
    case FOc.Got{l, k, z} <> rest:
      oc_ready(rest, info, OStep.ready.note(info, oc_node(l, k), rs))

def oc_lines(vs: List<&2, FOc.Line>) -> List<&2, ONode.Node>:
  match vs:
    case Nil{}:
      Nil{}
    case FOc.Line{l, k} <> rest:
      oc_node(l, k) <> oc_lines(rest)

# the opened chat: T, the built nodes, the view and whether it shrinks;
# the compaction view is the view merged down to its floor (OFit.fit, as
# every compaction view is); the ready merges; no call runs
def oc_open_at(+cfg: OState.Cfg, +t: List<&2, Bool>, +info: OInfo.Info, +view: List<&2, ONode.Node>, shrink: Bool, ready: List<&2, ONode.Node>) -> OState.St:
  OState.St{t, info, view, shrink, OFit.fit.view(OFit.Last{}, t, OState.Cfg.cfloor(cfg), OState.Cfg.ph(cfg), info, view), ready, Nil{}}

# a missed batch: the model's message batch (OStep.msg.go when a batch
# runs): the view merged down to its floor as far as built parents allow,
# still shrinking while over its floor
def oc_open_missed(r: List<&2, ONode.Node> & List<&2, ONode.Node>, +cfg: OState.Cfg, +t: List<&2, Bool>, +info: OInfo.Info, ready: List<&2, ONode.Node>) -> FOc.St & String:
  (merged, view0) = r
  +view = view0
  +s = oc_open_at(cfg, t, info, view, Nat.is_gt(OFit.view_size(OState.Cfg.ph(cfg), info, view), OState.Cfg.floor(cfg)), ready)
  (FOc.Live{cfg, s}, oc_spell_batch(True{}, merged, s))

def oc_open_go(missed: Bool, +cfg: OState.Cfg, +t: List<&2, Bool>, +info: OInfo.Info, +view: List<&2, ONode.Node>, shrink: Bool, ready: List<&2, ONode.Node>) -> FOc.St & String:
  match missed:
    case False{}:
      (FOc.Live{cfg, oc_open_at(cfg, t, info, view, shrink, ready)}, Wr.put_nat(0n, ""))
    case True{}:
      oc_open_missed(OFit.fit(OFit.Last{}, t, OState.Cfg.floor(cfg), OState.Cfg.ph(cfg), info, view), cfg, t, info, ready)

# the stepper and the reply an open asks: the loaded chat, and its missed
# batch run now when the log says one is missing
def oc_open_model(o: FOc.Open) -> FOc.St & String:
  match o:
    case FOc.Open{+cfg, t, +bs, vs, sh, m}:
      +info = oc_info(bs, OInfo.Info.empty())
      oc_open_go(m, cfg, OBits.Bits.of(t), info, oc_lines(vs), sh, oc_ready(bs, info, Nil{}))

# LAW optchat_entry_answers: in every state, every event or query that
# fits the wire, spelled, answers what the model answers and moves the
# chat as the model moves it: a message runs OStep.step's batch (the reply
# says whether one ran, its merges, the view after it and whether it
# still shrinks); a build, a start and a free are OStep.step's events; a
# wait stops exactly the busy nodes that are not view lines still unbuilt
# (OQueue.St.wait); the queries answer OQueue.cands, OQueue.cands.need,
# OCtx.ctx and the busy count, and move nothing
# EXCLUDES: a reply or a move other than the model's (a batch lost or
# invented, a node started twice, a merge offered while a turn waits, a
# needed call stopped, a compaction shown an unbuilt line), a query that
# moves the chat
law optchat_entry_answers:
  for +cfg: OState.Cfg
  for +s: OState.St
  for +q: FOc.Q
  for fits: {oc_fits(q) == True{} : Bool}
  {FOc.step(FOc.Live{cfg, s}, oc_spell(q)) == (FOc.Live{cfg, oc_next(cfg, s, q)}, oc_reply(cfg, s, q)) : FOc.St & String}

# the replies of the stepper st to the requests qs, spelled, in order
def oc_replies(qs: List<&2, FOc.Q>, +st: FOc.St) -> List<&2, String>:
  match qs:
    case Nil{}:
      Nil{}
    case +q <> rest:
      oc_reply_of(FOc.step(st, oc_spell(q))) <> oc_replies(rest, oc_state(FOc.step(st, oc_spell(q))))

# the replies the model asks for qs, in order, from the chat s
def oc_spec(qs: List<&2, FOc.Q>, +cfg: OState.Cfg, +s: OState.St) -> List<&2, String>:
  match qs:
    case Nil{}:
      Nil{}
    case +q <> rest:
      oc_reply(cfg, s, q) <> oc_spec(rest, cfg, oc_next(cfg, s, q))

def oc_all_fit(qs: List<&2, FOc.Q>) -> Bool:
  match qs:
    case Nil{}:
      True{}
    case q <> rest:
      Bool.and(oc_fits(q), oc_all_fit(rest))

# the sizes, T, the built nodes and the view lines of an open
def oc_cfg(o: FOc.Open) -> OState.Cfg:
  match o:
    case FOc.Open{c, t, bs, vs, sh, m}:
      c

def oc_t(o: FOc.Open) -> Nat:
  match o:
    case FOc.Open{c, t, bs, vs, sh, m}:
      t

def oc_built(o: FOc.Open) -> List<&2, FOc.Got>:
  match o:
    case FOc.Open{c, t, bs, vs, sh, m}:
      bs

def oc_view(o: FOc.Open) -> List<&2, FOc.Line>:
  match o:
    case FOc.Open{c, t, bs, vs, sh, m}:
      vs

# the model's chat an open asks (a refused open holds none)
def oc_chat(st: FOc.St) -> OState.St:
  match st:
    case FOc.Live{c, s}:
      s
    case FOc.Refused{}:
      OState.St.empty()

# LAW optchat_step_is_model: the stepper opened from any loaded chat and
# sent any events and queries, in any order, answers each as the model
# run from the opened chat answers it (the bridge's transcript, restated
# over every order)
# EXCLUDES: a stepper whose replies drift from the model's after some
# order of events, an open that starts the model elsewhere
law optchat_step_is_model:
  for +o: FOc.Open
  for +qs: List<&2, FOc.Q>
  for fits: {Bool.and(oc_open_fits(o), oc_all_fit(qs)) == True{} : Bool}
  {oc_replies(qs, oc_state(FOc.open(oc_spell_open(o)))) == oc_spec(qs, oc_cfg(o), oc_chat(oc_state(oc_open_model(o)))) : List<&2, String>}

# LAW optchat_open_is_model: an open that fits the wire opens the chat as
# loaded: the built nodes' sizes, the view, T; the compaction view is the
# view merged down to its floor; the ready merges are the built nodes
# noted as builds note them; no call runs; a missed batch (the log's last
# batch is open and older than the last message) runs as a message's
# batch runs, and is answered; else the open answers none
# EXCLUDES: a missed batch lost or run twice, a batch at an open that
# missed none, a compaction view that starts unfitted, a lost ready merge
law optchat_open_is_model:
  for +o: FOc.Open
  for fits: {oc_open_fits(o) == True{} : Bool}
  {FOc.open(oc_spell_open(o)) == oc_open_model(o) : FOc.St & String}

# p is the parent of a built node n of bs whose sibling is built, and is
# not built itself
def oc_pair_of(+info: OInfo.Info, bs: List<&2, FOc.Got>, +p: ONode.Node) -> Bool:
  match bs:
    case Nil{}:
      False{}
    case FOc.Got{+l, +k, z} <> rest:
      Bool.or(Bool.and(ONode.Node.eq(ONode.Node.parent(oc_node(l, k)), p), Bool.and(OInfo.Info.built(info, ONode.Node.sibling(oc_node(l, k))), Bool.not(OInfo.Info.built(info, ONode.Node.parent(oc_node(l, k)))))), oc_pair_of(info, rest, p))

# LAW optchat_open_ready: the ready merges of an opened chat are exactly
# the parents of built pairs that are not built themselves
# EXCLUDES: a ready merge lost at a restart (its pair built, the merge
# never started), a merge offered before both halves are built, a built
# node built again
law optchat_open_ready:
  for +o: FOc.Open
  for +p: ONode.Node
  for fits: {oc_open_fits(o) == True{} : Bool}
  {ONode.Nodes.has(OState.St.ready(oc_chat(oc_state(FOc.open(oc_spell_open(o))))), p) == oc_pair_of(oc_info(oc_built(o), OInfo.Info.empty()), oc_built(o), p) : Bool}

# the stepper fed the inputs xs, in order
def oc_feed(xs: List<&2, String>, st: FOc.St) -> FOc.St:
  match xs:
    case Nil{}:
      st
    case x <> rest:
      oc_feed(rest, oc_state(FOc.step(st, x)))

# the view lines vs tile the messages s..e-1: each node(l, k) starts
# where the one before ends (k·2^l) and covers 2^l messages
def oc_tiles(vs: List<&2, FOc.Line>, +s: Nat, +e: Nat) -> Bool:
  match vs:
    case Nil{}:
      Nat.is_eq(s, e)
    case FOc.Line{+l, +k} <> rest:
      Bool.and(Nat.is_eq(OBits.shl(l, k), s), oc_tiles(rest, Nat.add(s, OBits.pow2(l)), e))

# both views of the stepper's chat tile its messages 0..T (a refused open
# holds no chat)
def oc_covers(st: FOc.St) -> Type:
  match st:
    case FOc.Live{c, s}:
      S.Tiles(0n, OState.St.view(s), OBits.Bits.val(OState.St.t(s))) & S.Tiles(0n, OState.St.cview(s), OBits.Bits.val(OState.St.t(s)))
    case FOc.Refused{}:
      Unit

# LAW optchat_entry_covers: opened from a view that tiles the chat, the
# stepper's view and compaction view tile the messages 0..T after any
# inputs whatsoever, in any order: events, queries, garbage
# (view_covers and cview_covers, restated over the shipped entry and every
# input)
# EXCLUDES: a message lost, doubled or out of order in either view after
# some order of events (a batch that splits or skips a line, a missed
# batch that breaks the view, garbage read as an event)
law optchat_entry_covers:
  for +o: FOc.Open
  for +xs: List<&2, String>
  for fits: {oc_open_fits(o) == True{} : Bool}
  for tiles: {oc_tiles(oc_view(o), 0n, oc_t(o)) == True{} : Bool}
  oc_covers(oc_feed(xs, oc_state(FOc.open(oc_spell_open(o)))))

# LAW optchat_bits_of: a node index read from the wire is the index the
# model holds: its bits' value is the number, with no high zero bit
# EXCLUDES: a misread index (reversed or dropped bits), a padded one the
# built nodes' tries file under another key
law optchat_bits_of:
  for +n: Nat
  {OBits.Bits.val(OBits.Bits.of(n)) == n : Nat} & {S.Bits.canon(OBits.Bits.of(n)) == True{} : Bool}

# The entry: the laws' reader, from the wire's primitives

def oc_read.k(l: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<FOc.Line>:
  match r:
    case Wr.Got{k, s}:
      Wr.Got{FOc.Line{l, k}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def oc_read.l(r: Wr.Dec<Nat>) -> Wr.Dec<FOc.Line>:
  match r:
    case Wr.Got{l, s}:
      oc_read.k(l, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

# a node: two Nats
def oc_read.line(s: String) -> Wr.Dec<FOc.Line>:
  oc_read.l(Wr.get_nat(s))

def oc_read.size(n: FOc.Line, r: Wr.Dec<Nat>) -> Wr.Dec<FOc.Got>:
  match n r:
    case FOc.Line{l, k} Wr.Got{z, s}:
      Wr.Got{FOc.Got{l, k, z}, s}
    case FOc.Line{l, k} Wr.Bad{}:
      Wr.Bad{}

def oc_read.got.node(r: Wr.Dec<FOc.Line>) -> Wr.Dec<FOc.Got>:
  match r:
    case Wr.Got{n, s}:
      oc_read.size(n, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

# a built node: three Nats
def oc_read.got(s: String) -> Wr.Dec<FOc.Got>:
  oc_read.got.node(oc_read.line(s))

def oc_read.built(r: Wr.Dec<FOc.Got>) -> Wr.Dec<FOc.Q>:
  match r:
    case Wr.Got{g, s}:
      match g:
        case FOc.Got{l, k, z}:
          Wr.Got{FOc.QBuilt{l, k, z}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def oc_read.start(r: Wr.Dec<FOc.Line>) -> Wr.Dec<FOc.Q>:
  match r:
    case Wr.Got{n, s}:
      match n:
        case FOc.Line{l, k}:
          Wr.Got{FOc.QStart{l, k}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def oc_read.free(r: Wr.Dec<FOc.Line>) -> Wr.Dec<FOc.Q>:
  match r:
    case Wr.Got{n, s}:
      match n:
        case FOc.Line{l, k}:
          Wr.Got{FOc.QFree{l, k}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def oc_read.ctx(r: Wr.Dec<FOc.Line>) -> Wr.Dec<FOc.Q>:
  match r:
    case Wr.Got{n, s}:
      match n:
        case FOc.Line{l, k}:
          Wr.Got{FOc.QCtx{l, k}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def oc_read.tag(n: Nat, s: String) -> Wr.Dec<FOc.Q>:
  match n:
    case 0n:
      Wr.Got{FOc.QMsg{}, s}
    case 1n:
      oc_read.built(oc_read.got(s))
    case 2n:
      oc_read.start(oc_read.line(s))
    case 3n:
      oc_read.free(oc_read.line(s))
    case 4n:
      Wr.Got{FOc.QWait{}, s}
    case 5n:
      Wr.Got{FOc.QCands{}, s}
    case 6n:
      Wr.Got{FOc.QNeed{}, s}
    case 7n:
      oc_read.ctx(oc_read.line(s))
    case 8n:
      Wr.Got{FOc.QBusy{}, s}
    case 9n+p:
      Wr.Bad{}

def oc_read.go(r: Wr.Dec<Nat>) -> Wr.Dec<FOc.Q>:
  match r:
    case Wr.Got{n, s}:
      oc_read.tag(n, s)
    case Wr.Bad{}:
      Wr.Bad{}

def oc_read.end(whole: Bool, q: FOc.Q) -> Maybe<&2, FOc.Q>:
  match whole:
    case True{}:
      Some{q}
    case False{}:
      None{}

def oc_read.whole(d: Wr.Dec<FOc.Q>) -> Maybe<&2, FOc.Q>:
  match d:
    case Wr.Got{q, s}:
      oc_read.end(Wr.end(s), q)
    case Wr.Bad{}:
      None{}

# the event or query s is, when s is exactly one
def oc_read(s: String) -> Maybe<&2, FOc.Q>:
  oc_read.whole(oc_read.go(Wr.get_nat(s)))

# LAW optchat_entry_reads: in every state, an input the laws' reader reads
# as exactly one event or query is answered as the model answers it
# EXCLUDES: an input read otherwise by the entry than by the wire's
# grammar, a reply or a move other than the model's
law optchat_entry_reads:
  for +cfg: OState.Cfg
  for +s: OState.St
  for +i: String
  for +q: FOc.Q
  for got: {oc_read(i) == Some{q} : Maybe<&2, FOc.Q>}
  {FOc.step(FOc.Live{cfg, s}, i) == (FOc.Live{cfg, oc_next(cfg, s, q)}, oc_reply(cfg, s, q)) : FOc.St & String}

# LAW optchat_entry_malformed_exact: in every state, an input the laws'
# reader does not read as exactly one event or query (a bad tag, a short
# or bad Nat, input left over) keeps the chat and answers exactly the
# error form 'E ' + "optchat: malformed event"
# EXCLUDES: a guessed event (garbage read as a message that runs a batch,
# as a build, as a wait that stops calls), a chat moved by garbage,
# another error text
law optchat_entry_malformed_exact:
  for +cfg: OState.Cfg
  for +s: OState.St
  for +i: String
  for no: {oc_read(i) == None{} : Maybe<&2, FOc.Q>}
  {FOc.step(FOc.Live{cfg, s}, i) == (FOc.Live{cfg, s}, SCon{'E', SCon{' ', "optchat: malformed event"}}) : FOc.St & String}

def oc_read_open.missed(c: OState.Cfg, t: Nat, bs: List<&2, FOc.Got>, vs: List<&2, FOc.Line>, sh: Bool, r: Wr.Dec<Bool>) -> Wr.Dec<FOc.Open>:
  match r:
    case Wr.Got{m, s}:
      Wr.Got{FOc.Open{c, t, bs, vs, sh, m}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def oc_read_open.shrink(c: OState.Cfg, t: Nat, bs: List<&2, FOc.Got>, vs: List<&2, FOc.Line>, r: Wr.Dec<Bool>) -> Wr.Dec<FOc.Open>:
  match r:
    case Wr.Got{sh, s}:
      oc_read_open.missed(c, t, bs, vs, sh, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def oc_read_open.view(c: OState.Cfg, t: Nat, bs: List<&2, FOc.Got>, r: Wr.Dec<List<&2, FOc.Line>>) -> Wr.Dec<FOc.Open>:
  match r:
    case Wr.Got{vs, s}:
      oc_read_open.shrink(c, t, bs, vs, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def oc_read_open.built(c: OState.Cfg, t: Nat, r: Wr.Dec<List<&2, FOc.Got>>) -> Wr.Dec<FOc.Open>:
  match r:
    case Wr.Got{bs, s}:
      oc_read_open.view(c, t, bs, Wr.get_list(~FOc.Line, ~oc_read.line, s))
    case Wr.Bad{}:
      Wr.Bad{}

def oc_read_open.t(c: OState.Cfg, r: Wr.Dec<Nat>) -> Wr.Dec<FOc.Open>:
  match r:
    case Wr.Got{t, s}:
      oc_read_open.built(c, t, Wr.get_list(~FOc.Got, ~oc_read.got, s))
    case Wr.Bad{}:
      Wr.Bad{}

def oc_read_cfg.jobs(a: Nat, b: Nat, c: Nat, d: Nat, e: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<OState.Cfg>:
  match r:
    case Wr.Got{f, s}:
      Wr.Got{OState.Cfg{a, b, c, d, e, f}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def oc_read_cfg.cfloor(a: Nat, b: Nat, c: Nat, d: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<OState.Cfg>:
  match r:
    case Wr.Got{e, s}:
      oc_read_cfg.jobs(a, b, c, d, e, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def oc_read_cfg.cceil(a: Nat, b: Nat, c: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<OState.Cfg>:
  match r:
    case Wr.Got{d, s}:
      oc_read_cfg.cfloor(a, b, c, d, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def oc_read_cfg.floor(a: Nat, b: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<OState.Cfg>:
  match r:
    case Wr.Got{c, s}:
      oc_read_cfg.cceil(a, b, c, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def oc_read_cfg.ceil(a: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<OState.Cfg>:
  match r:
    case Wr.Got{b, s}:
      oc_read_cfg.floor(a, b, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def oc_read_cfg.ph(r: Wr.Dec<Nat>) -> Wr.Dec<OState.Cfg>:
  match r:
    case Wr.Got{a, s}:
      oc_read_cfg.ceil(a, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def oc_read_open.cfg(r: Wr.Dec<OState.Cfg>) -> Wr.Dec<FOc.Open>:
  match r:
    case Wr.Got{c, s}:
      oc_read_open.t(c, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def oc_read_open.end(whole: Bool, o: FOc.Open) -> Maybe<&2, FOc.Open>:
  match whole:
    case True{}:
      Some{o}
    case False{}:
      None{}

def oc_read_open.whole(d: Wr.Dec<FOc.Open>) -> Maybe<&2, FOc.Open>:
  match d:
    case Wr.Got{o, s}:
      oc_read_open.end(Wr.end(s), o)
    case Wr.Bad{}:
      None{}

# the open s is, when s is exactly one
def oc_read_open(s: String) -> Maybe<&2, FOc.Open>:
  oc_read_open.whole(oc_read_open.cfg(oc_read_cfg.ph(Wr.get_nat(s))))

# LAW optchat_entry_open_reads: an open input the laws' reader reads as
# exactly one open opens the chat that open loads
# EXCLUDES: an open read otherwise by the entry than by the wire's grammar
law optchat_entry_open_reads:
  for +i: String
  for +o: FOc.Open
  for got: {oc_read_open(i) == Some{o} : Maybe<&2, FOc.Open>}
  {FOc.open(i) == oc_open_model(o) : FOc.St & String}

# LAW optchat_entry_open_malformed_exact: an open input the laws' reader
# does not read as exactly one open opens the refused state and answers
# exactly the error form 'E ' + "optchat: malformed open"
# EXCLUDES: a default chat (an empty one, or garbage sizes) opened for
# garbage, a batch run for garbage
law optchat_entry_open_malformed_exact:
  for +i: String
  for no: {oc_read_open(i) == None{} : Maybe<&2, FOc.Open>}
  {FOc.open(i) == (FOc.Refused{}, SCon{'E', SCon{' ', "optchat: malformed open"}}) : FOc.St & String}

# LAW optchat_entry_shut: a refused open answers every step with exactly
# the error form 'E ' + "optchat: the open was refused"
# EXCLUDES: a refused stepper that answers a batch or nodes to start
law optchat_entry_shut:
  for +i: String
  {FOc.step(FOc.Refused{}, i) == (FOc.Refused{}, SCon{'E', SCon{' ', "optchat: the open was refused"}}) : FOc.St & String}

# the replies of the stepper st to the inputs xs, in order
def oc_answers(xs: List<&2, String>, +st: FOc.St) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> rest:
      oc_reply_of(FOc.step(st, x)) <> oc_answers(rest, oc_state(FOc.step(st, x)))

# a small chat: placeholder 1 byte, view 3 down to 2, compaction view 3
# down to 1, 2 jobs; messages 0 and 1 built, 1 byte each, each its own
# line; no batch shrinks it, none was missed
def oc_small() -> String:
  "1,3,2,3,1,2,2,2,0,0,1,0,1,1,2,0,0,0,1,FF"

# LAW optchat_entry_example: anchor: the bytes the chat sends and the
# replies: opens of the small chat and of garbage, a step of the refused
# stepper; on the small chat: the nodes to start (the merge 0+2), the
# nodes a waiting turn may start (none), the merge's call started, the
# busy count, a wait that stops it, the busy count, the merge built,
# message 2 (no batch: 3 bytes), message 3 (a batch merges 0+2 and stays
# over its floor: 2+1 is not built), a compaction's view of 3+1 (stops at
# the unbuilt 2+1), a bad tag, input left over
# EXCLUDES: an entry that answers other bytes than the grammar's
law optchat_entry_example:
  {[oc_reply_of(FOc.open(oc_small())), oc_reply_of(FOc.open("x")), oc_reply_of(FOc.step(oc_state(FOc.open("x")), "0,"))] == ["0,", SCon{'E', SCon{' ', "optchat: malformed open"}}, SCon{'E', SCon{' ', "optchat: the open was refused"}}] : List<&2, String>} & {oc_answers(["5,", "6,", "2,1,0,", "8,", "4,", "8,", "1,1,0,1,", "0,", "0,", "7,0,3,", "9,", "0,x"], oc_state(FOc.open(oc_small()))) == ["1,1,0,", "0,", "0,", "1,", "1,1,0,", "0,", "0,", "0,", "1,1,1,0,3,1,0,0,2,0,3,T", "1,1,0,", SCon{'E', SCon{' ', "optchat: malformed event"}}, SCon{'E', SCon{' ', "optchat: malformed event"}}] : List<&2, String>}
