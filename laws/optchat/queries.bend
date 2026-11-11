# eukhe: the laws of area optchat: what the planner answers and how it
# moves
#
# The stepper bend/ffi_optchat.bend answers each query and moves the chat
# on each event as the model does (optchat_entry_answers,
# optchat_step_is_model in laws/optchat.bend). These laws pin the model,
# for every state, by what each answer and move must be (the
# requirements R1-R9, A3-A5 of laws/optchat.bend; spec/memory/optchat.bend
# restates the gist without the code): the nodes to start (QCands,
# QNeed), a compaction's view (QCtx), the busy calls after a call starts
# (QStart), is freed (QFree) or a turn starts to wait (QWait), the size
# each built node has, a fit (a chain of merges of the most due pair), a
# message's batch and the compaction sawtooth, and a build.

import Base
import ../../bend/optchat/bits.bend as OBits
import ../../bend/optchat/node.bend as ONode
import ../../bend/optchat/info.bend as OInfo
import ../../bend/optchat/fit.bend as OFit
import ../../bend/optchat/state.bend as OState
import ../../bend/optchat/step.bend as OStep
import ../../bend/optchat/queue.bend as OQueue
import ../../bend/optchat/ctx.bend as OCtx
import ../../spec/memory/optchat.bend as S

# The work queue (R7, R6)
# -----------------------

# LAW optchat_cands_spec: in every state, the nodes to start are the
# view's unbuilt lines not running with fewer than jobs unbuilt lines
# before them, oldest first, then the ready merges not running, in their
# order, as many as the free job slots (jobs less the running calls)
# EXCLUDES: a merge started before a waiting message's line, a running
# node started again, more calls than jobs, a ready merge never started
# (memory that never compacts), a line started past jobs unbuilt lines,
# the order turned around
law optchat_cands_spec:
  for +cfg: OState.Cfg
  for +s: OState.St
  {OQueue.cands(cfg, s) == S.cands(cfg, s) : List<&2, ONode.Node>}

# LAW optchat_need_spec: in every state, the nodes to start while a turn
# waits are the view's lines of optchat_cands_spec alone: the ready
# merges wait
# EXCLUDES: a merge started while a turn waits for the view, a needed
# line left out (a turn that waits forever), more calls than jobs
law optchat_need_spec:
  for +cfg: OState.Cfg
  for +s: OState.St
  {OQueue.cands.need(cfg, s) == S.need(cfg, s) : List<&2, ONode.Node>}

# A compaction's view (R8)
# ------------------------

# LAW optchat_ctx_exact: in every state, a compaction's view of node(l, i)
# is the longest start of the compaction view whose lines are all built
# and end by the node's bound (message i for a message's node, its last
# message, (i+1)·2^l, for a merge's): a prefix of the compaction view,
# each line built and ending by the bound, and the compaction view's next
# line, if any, unbuilt or ending past it
# EXCLUDES: an empty or cut view (a compaction that loses context it may
# see), a line past the node (a message shown to its own compaction), an
# unbuilt line, a line after a gap, a view read from the view instead of
# the compaction view
law optchat_ctx_exact:
  for +s: OState.St
  for +n: ONode.Node
  S.CtxOf(OState.St.info(s), S.ctx_bound(n), OCtx.ctx(s, n), OState.St.cview(s))

# The calls (A3)
# --------------

# the chat after one event, and the merges it answers
def oc_after(+cfg: OState.Cfg, +s: OState.St, e: OState.Ev) -> OState.St:
  Pair.fst(OState.St, List<&2, ONode.Node>, OStep.step(cfg, s, e))

def oc_merged(+cfg: OState.Cfg, +s: OState.St, e: OState.Ev) -> List<&2, ONode.Node>:
  Pair.snd(OState.St, List<&2, ONode.Node>, OStep.step(cfg, s, e))

# LAW optchat_start_counts: in every state, when node n's call starts,
# every node m keeps its count of busy calls (by level and index value),
# except n, which gains one call when it ran none (a node already busy
# stays as it was); nothing but the busy calls changes; no batch runs
# EXCLUDES: a node counted twice in the busy calls (a job slot lost), a
# start that is not recorded, another node's call dropped, a start that
# moves the view or runs a batch
law optchat_start_counts:
  for +cfg: OState.Cfg
  for +s: OState.St
  for +n: ONode.Node
  for +m: ONode.Node
  {oc_after(cfg, s, OState.Start{n}) == S.with_busy(s, OState.St.busy(oc_after(cfg, s, OState.Start{n}))) : OState.St} & ({oc_merged(cfg, s, OState.Start{n}) == Nil{} : List<&2, ONode.Node>} & {S.count(OState.St.busy(oc_after(cfg, s, OState.Start{n})), m) == S.one_if(Bool.and(S.same(m, n), Bool.not(S.member(OState.St.busy(s), n))), S.count(OState.St.busy(s), m)) : Nat})

# LAW optchat_free_counts: in every state, when node n's call is freed, n
# has no busy call left (no copy), every other node keeps its count;
# nothing but the busy calls changes; no batch runs
# EXCLUDES: a freed node still counted busy (a node never retried, a job
# slot lost), another node freed, a free that moves the view
law optchat_free_counts:
  for +cfg: OState.Cfg
  for +s: OState.St
  for +n: ONode.Node
  for +m: ONode.Node
  {oc_after(cfg, s, OState.Free{n}) == S.with_busy(s, OState.St.busy(oc_after(cfg, s, OState.Free{n}))) : OState.St} & ({oc_merged(cfg, s, OState.Free{n}) == Nil{} : List<&2, ONode.Node>} & {S.count(OState.St.busy(oc_after(cfg, s, OState.Free{n})), m) == S.zero_if(S.same(m, n), S.count(OState.St.busy(s), m)) : Nat})

# LAW optchat_wait_keeps_needed: in every state, when a turn starts to
# wait, every busy call of a node the turn needs (a view line, by level
# and index value, still unbuilt) stays, every other is stopped and
# answered: per node m (its level and index bits), the calls kept are
# m's calls if m is needed, else none, and the calls kept and the calls
# answered add up to m's calls; nothing but the busy calls changes
# EXCLUDES: a needed call stopped (a turn that waits forever), a merge
# kept running while a turn waits, a call stopped but not answered (a
# summary the chat never cancels), a call answered twice, the view or the
# sizes changed
law optchat_wait_keeps_needed:
  for +s: OState.St
  for +m: ONode.Node
  {OQueue.St.wait(s) == S.with_busy(s, OState.St.busy(OQueue.St.wait(s))) : OState.St} & ({S.copies(OState.St.busy(OQueue.St.wait(s)), m) == S.zero_if(Bool.not(Bool.and(S.member(OState.St.view(s), m), Bool.not(OInfo.Info.built(OState.St.info(s), m)))), S.copies(OState.St.busy(s), m)) : Nat} & {Nat.add(S.copies(OQueue.St.held(s), m), S.copies(OState.St.busy(OQueue.St.wait(s)), m)) == S.copies(OState.St.busy(s), m) : Nat})

# The built nodes' sizes (A5)
# ---------------------------

# LAW optchat_info_set_get: the built nodes' sizes are a map from a node
# (its level and its index bits) to its size: once node n is built with
# z bytes, n has z bytes and every other node keeps what it had (the
# chat's sizes: every info but the push comparison's All)
# EXCLUDES: a size filed under another node (a merge offered before its
# halves are built, a line counted at another's size), a size lost or
# changed when another node is built, a rebuilt node keeping its old size
law optchat_info_set_get:
  for +ts: List<&2, OInfo.Trie>
  for +n: ONode.Node
  for +z: Nat
  for +m: ONode.Node
  {OInfo.Info.get(OInfo.Info.set(OInfo.Lvls{ts}, n, z), m) == S.info_after(n, z, m, OInfo.Info.get(OInfo.Lvls{ts}, m)) : Maybe<&2, Nat>}

# LAW optchat_info_empty: no node of an empty chat is built
# EXCLUDES: a chat that opens with a node built (a merge offered before
# any summary)
law optchat_info_empty:
  for +m: ONode.Node
  {OInfo.Info.get(OInfo.Info.empty(), m) == None{} : Maybe<&2, Nat>}

# A fit (R2, R3, R4)
# ------------------

# LAW optchat_fit_chain: every fit, for either due measure, any T, budget,
# placeholder size, built sizes and view, is a chain of merges (S.Chain):
# while the view takes more than the budget (a line counts its node's
# bytes, the placeholder's while unbuilt), it replaces the most due pair
# of adjacent sibling lines whose parent is built by that parent (S.At:
# every such pair before it strictly less due, none after it more due;
# due = (T - last) / 2^l for Last, from the pair's first message for
# First, compared as rationals); it answers the merged parents in merge
# order; it stops within the budget, or when no pair may merge
# EXCLUDES: a merge of a less due pair, ties broken toward the newer
# pair, a merge of lines that are not siblings or whose parent is
# unbuilt, a merge past the budget or one too few, merges answered other
# than made, a size counted otherwise
law optchat_fit_chain:
  for +m: OFit.Age
  for +t: List<&2, Bool>
  for +budget: Nat
  for +ph: Nat
  for +info: OInfo.Info
  for +v: List<&2, ONode.Node>
  S.Chain(m, t, info, budget, ph, v, Pair.fst(List<&2, ONode.Node>, List<&2, ONode.Node>, OFit.fit(m, t, budget, ph, info, v)), Pair.snd(List<&2, ONode.Node>, List<&2, ONode.Node>, OFit.fit(m, t, budget, ph, info, v)))

# A message (R5)
# --------------

# LAW optchat_message_counts: in every state, a message adds one to T
# and changes neither the built sizes, the ready merges nor the busy
# calls
# EXCLUDES: a message lost or counted twice (T off), a size, a ready
# merge or a call lost at a message
law optchat_message_counts:
  for +cfg: OState.Cfg
  for +s: OState.St
  {OBits.Bits.val(OState.St.t(oc_after(cfg, s, OState.Msg{}))) == 1n+OBits.Bits.val(OState.St.t(s)) : Nat} & ({OState.St.info(oc_after(cfg, s, OState.Msg{})) == OState.St.info(s) : OInfo.Info} & ({OState.St.ready(oc_after(cfg, s, OState.Msg{})) == OState.St.ready(s) : List<&2, ONode.Node>} & {OState.St.busy(oc_after(cfg, s, OState.Msg{})) == OState.St.busy(s) : List<&2, ONode.Node>}))

# LAW optchat_message_quiet: in every state where no batch runs (the view
# is not shrinking, and with the message's line it stays within ceil), a
# message merges nothing, appends its own line to the view (which stops
# shrinking), and the compaction view, with the line appended, keeps its
# sawtooth (past cceil it is fitted down to cfloor, else it stays)
# EXCLUDES: a batch at a message under ceil, a message lost from either
# view, a compaction view left past cceil or merged under it
law optchat_message_quiet:
  for +cfg: OState.Cfg
  for +s: OState.St
  for quiet: {S.batch(cfg, s) == False{} : Bool}
  {oc_merged(cfg, s, OState.Msg{}) == Nil{} : List<&2, ONode.Node>} & ({OState.St.view(oc_after(cfg, s, OState.Msg{})) == S.grown(s) : List<&2, ONode.Node>} & ({OState.St.shrink(oc_after(cfg, s, OState.Msg{})) == False{} : Bool} & S.Saw(cfg, OState.St.t(oc_after(cfg, s, OState.Msg{})), OState.St.info(s), S.cgrown(s), OState.St.cview(oc_after(cfg, s, OState.Msg{})))))

# LAW optchat_message_batch: in every state where a batch runs (the view
# is still shrinking, or the message's line takes it past ceil), the view
# with the message's line is fitted down to floor (optchat_fit_chain's
# chain, at the new T: the merges answered are the chain's parents); the
# view still shrinks exactly while it is over floor; when the batch
# merged anything the compaction view restarts from the new view fitted
# down to cfloor, else it keeps its sawtooth with the message's line
# EXCLUDES: a shrinking view left alone, a batch that fits to another
# budget, a shrink flag kept wrong, a compaction view not restarted after
# a batch, merges answered other than made
law optchat_message_batch:
  for +cfg: OState.Cfg
  for +s: OState.St
  for runs: {S.batch(cfg, s) == True{} : Bool}
  S.Chain(OFit.Last{}, OState.St.t(oc_after(cfg, s, OState.Msg{})), OState.St.info(s), OState.Cfg.floor(cfg), OState.Cfg.ph(cfg), S.grown(s), oc_merged(cfg, s, OState.Msg{}), OState.St.view(oc_after(cfg, s, OState.Msg{}))) & ({OState.St.shrink(oc_after(cfg, s, OState.Msg{})) == Nat.is_gt(S.vsize(OState.Cfg.ph(cfg), OState.St.info(s), OState.St.view(oc_after(cfg, s, OState.Msg{}))), OState.Cfg.floor(cfg)) : Bool} & S.Restart(oc_merged(cfg, s, OState.Msg{}), cfg, OState.St.t(oc_after(cfg, s, OState.Msg{})), OState.St.info(s), OState.St.view(oc_after(cfg, s, OState.Msg{})), S.cgrown(s), OState.St.cview(oc_after(cfg, s, OState.Msg{}))))

# A build (A4, A3, R5)
# --------------------

# LAW optchat_sibling: a node's sibling is the other half of its parent:
# the same level, index k+1 for an even k, k-1 for an odd one
# EXCLUDES: a merge readied by the wrong half (the node itself, a cousin,
# another level)
law optchat_sibling:
  for +n: ONode.Node
  {S.lvl(ONode.Node.sibling(n)) == S.lvl(n) : Nat} & {S.idx(ONode.Node.sibling(n)) == S.other(S.idx(n)) : Nat}

# LAW optchat_build_notes: in every chat state (its built sizes a map:
# S.is_map, as every chat's are; the push comparison's All, which counts
# every node 1 byte, is no chat's), when node n is built with size bytes,
# n has size bytes and every other node keeps its size (by level and
# index bits); n has no busy call left, every other node keeps its count;
# T, the view and shrink stay; the compaction view keeps its sawtooth
# under the new sizes; no batch runs
# EXCLUDES: a size lost or filed elsewhere, a built node still busy (a
# slot lost), a view moved by a build, a compaction view left past cceil
law optchat_build_notes:
  for +cfg: OState.Cfg
  for +s: OState.St
  for +n: ONode.Node
  for +size: Nat
  for +m: ONode.Node
  for map: {S.is_map(OState.St.info(s)) == True{} : Bool}
  {oc_merged(cfg, s, OState.Build{n, size}) == Nil{} : List<&2, ONode.Node>} & ({OState.St.t(oc_after(cfg, s, OState.Build{n, size})) == OState.St.t(s) : List<&2, Bool>} & ({OState.St.view(oc_after(cfg, s, OState.Build{n, size})) == OState.St.view(s) : List<&2, ONode.Node>} & ({OState.St.shrink(oc_after(cfg, s, OState.Build{n, size})) == OState.St.shrink(s) : Bool} & ({OInfo.Info.get(OState.St.info(oc_after(cfg, s, OState.Build{n, size})), m) == S.info_after(n, size, m, OInfo.Info.get(OState.St.info(s), m)) : Maybe<&2, Nat>} & ({S.count(OState.St.busy(oc_after(cfg, s, OState.Build{n, size})), m) == S.zero_if(S.same(m, n), S.count(OState.St.busy(s), m)) : Nat} & S.Saw(cfg, OState.St.t(s), OState.St.info(oc_after(cfg, s, OState.Build{n, size})), OState.St.cview(s), OState.St.cview(oc_after(cfg, s, OState.Build{n, size}))))))))

# LAW optchat_build_ready: in every state, after node n is built, a node p
# is a ready merge exactly when it was one and is not n, or it is n's
# parent, n's sibling is built and the parent is not (by level and index
# value)
# EXCLUDES: a ready merge lost or offered before both halves are built, a
# built node still offered, a built parent offered again
law optchat_build_ready:
  for +cfg: OState.Cfg
  for +s: OState.St
  for +n: ONode.Node
  for +size: Nat
  for +p: ONode.Node
  {S.member(OState.St.ready(oc_after(cfg, s, OState.Build{n, size})), p) == Bool.or(Bool.and(S.member(OState.St.ready(s), p), Bool.not(S.same(p, n))), Bool.and(S.same(p, S.parent(n)), Bool.and(OInfo.Info.built(OState.St.info(oc_after(cfg, s, OState.Build{n, size})), ONode.Node.sibling(n)), Bool.not(OInfo.Info.built(OState.St.info(oc_after(cfg, s, OState.Build{n, size})), S.parent(n)))))) : Bool}

# LAW optchat_build_ready_sorted: a build keeps the ready merges in level,
# then index order, each once (the queue starts lower merges first)
# EXCLUDES: a ready merge noted twice (two calls for one merge), a merge
# filed out of order (a higher merge started before a lower one)
law optchat_build_ready_sorted:
  for +cfg: OState.Cfg
  for +s: OState.St
  for +n: ONode.Node
  for +size: Nat
  for sorted: {S.Sorted(OState.St.ready(s)) == True{} : Bool}
  {S.Sorted(OState.St.ready(oc_after(cfg, s, OState.Build{n, size}))) == True{} : Bool}
