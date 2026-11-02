# eukhe: the laws of area optchat: what the planner answers
#
# The stepper bend/ffi_optchat.bend answers each query and moves the chat
# on each event as the model does (optchat_entry_answers,
# optchat_entry_reads, optchat_step_is_model in laws/optchat.bend). These
# laws pin the model's query replies, its call bookkeeping and its map of
# built sizes, for every state, to the restatement of the gist in
# spec/memory/optchat.bend (the work queue and a compaction's view, gist
# §4; LAWS.bend H2): the nodes to start (QCands, QNeed), a compaction's
# view (QCtx), the busy set after a call starts (QStart), is freed (QFree)
# or a turn starts to wait (QWait), and the size each built node has.

import Base
import ../../bend/optchat/node.bend as ONode
import ../../bend/optchat/info.bend as OInfo
import ../../bend/optchat/state.bend as OState
import ../../bend/optchat/step.bend as OStep
import ../../bend/optchat/queue.bend as OQueue
import ../../bend/optchat/ctx.bend as OCtx
import ../../spec/memory/optchat.bend as S

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

# LAW optchat_ctx_spec: in every state, a compaction's view of node(l, i)
# is the compaction view's lines from the first on that end by its bound
# (message i for a message's node, else its last message, (i+1)·2^l) and
# are built, up to the first that does not or is not
# EXCLUDES: an empty or cut view (a compaction that loses the context it
# may see), a line past the node, an unbuilt line, a line after a gap
law optchat_ctx_spec:
  for +s: OState.St
  for +n: ONode.Node
  {OCtx.ctx(s, n) == S.ctx(s, n) : List<&2, ONode.Node>}

# LAW optchat_wait_spec: in every state, a turn that starts to wait
# keeps busy exactly the busy nodes that are view lines still unbuilt, in
# their order, and changes nothing else
# EXCLUDES: a needed call stopped (a turn that waits forever), a merge
# kept running while a turn waits, the view or the sizes changed
law optchat_wait_spec:
  for +s: OState.St
  {OQueue.St.wait(s) == S.wait(s) : OState.St}

# LAW optchat_start_spec: in every state, a node's call that starts makes
# the node busy once (a node already busy stays once) and changes nothing
# else; it runs no batch
# EXCLUDES: a node counted twice in the busy calls (a job slot lost), a
# start that moves the view
law optchat_start_spec:
  for +cfg: OState.Cfg
  for +s: OState.St
  for +n: ONode.Node
  {OStep.step(cfg, s, OState.Start{n}) == (S.with_busy(s, S.busy_add(OState.St.busy(s), n)), Nil{}) : OState.St & List<&2, ONode.Node>}

# LAW optchat_free_spec: in every state, a node's call that is freed
# leaves the busy calls without the node (every copy) and changes nothing
# else; it runs no batch
# EXCLUDES: a freed node still counted busy (a node never retried, a job
# slot lost), another node freed, a free that moves the view
law optchat_free_spec:
  for +cfg: OState.Cfg
  for +s: OState.St
  for +n: ONode.Node
  {OStep.step(cfg, s, OState.Free{n}) == (S.with_busy(s, S.busy_del(OState.St.busy(s), n)), Nil{}) : OState.St & List<&2, ONode.Node>}

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
