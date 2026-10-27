# eukhe: the laws of area optchat

import Base
import ../bend/compactor.bend as C
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
# LAWS.bend H2: the need-first queue of bend/optchat/queue.bend, the settle
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
