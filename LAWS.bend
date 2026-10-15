# LAWS: what eukhe's chat memory must do, after Victor Taelin's OptChat
# gist. Each law is an open claim about the model in bend/optchat.bend;
# PROOF.bend proves them all. docs/memory.md maps each gist rule to the
# Rust code and to the law (or test) that secures it.
#
#   bend PROOF.bend             checks every proof
#   bend PROOF.bend --verdict   checks them again with the proven kernel

import Base
import ./bend/optchat.bend as O
import ./bend/spec.bend as S

# (a) The view
# ------------

# LAW: after any history, the view covers messages 0..T-1 exactly once,
# contiguous, oldest first, every line an aligned tree node (gist §3)
law view_covers:
  for +cfg: O.Cfg
  for +evs: List<&2, O.Ev>
  S.Tiles(0n, S.view.of(cfg, evs), S.total.of(cfg, evs))

# LAW: so does the compaction view (gist §4)
law cview_covers:
  for +cfg: O.Cfg
  for +evs: List<&2, O.Ev>
  S.Tiles(0n, S.cview.of(cfg, evs), S.total.of(cfg, evs))

# (b) A message
# -------------

# LAW: when no batch runs, a message only appends its own line: the
# old view is a prefix of the new one (gist §3.2, §3.3)
law message_appends:
  for +cfg: O.Cfg
  for +s: O.St
  for quiet: {O.St.batch(cfg, s) == False{} : Bool}
  {O.St.view(Pair.fst(O.St, List<&2, O.Node>, O.msg(cfg, s))) == List.append(&2, O.Node, O.St.view(s), [O.Node.leaf(O.St.t(s))]) : List<&2, O.Node>}

# LAW: and it merges nothing
law message_merges_nothing:
  for +cfg: O.Cfg
  for +s: O.St
  for quiet: {O.St.batch(cfg, s) == False{} : Bool}
  {Pair.snd(O.St, List<&2, O.Node>, O.msg(cfg, s)) == Nil{} : List<&2, O.Node>}

# (c) A merge
# -----------

# LAW: a merge replaces two sibling lines by their built parent, or
# changes nothing (gist §3.1)
law merge_is_one_pair:
  for +info: O.Info
  for +v: List<&2, O.Node>
  for +a: O.Node
  Or({O.merge(info, v, a) == v : List<&2, O.Node>}, S.Merged(info, v, O.merge(info, v, a)))

# LAW: a merge keeps the coverage
law merge_covers:
  for +info: O.Info
  for +s: Nat
  for +v: List<&2, O.Node>
  for +w: List<&2, O.Node>
  for +e: Nat
  for tiles: S.Tiles(s, v, e)
  for merged: S.Merged(info, v, w)
  S.Tiles(s, w, e)

# (d) Taelin's push
# -----------------

# LAW: with push's list length as the budget (a line counts 1 byte,
# every node built), the due order (T - last) / 2^l makes exactly the
# merges of Taelin's rollback push, at every step t = 0..20,000 (gist
# §3.2: "checked for t = 0..20,000"). Bounded: proven by computation.
law push_agrees:
  {O.agree(O.Last{}, 20001n) == True{} : Bool}

# (e) A batch
# -----------

# LAW: a fit ends at most at its budget, unless no pair can merge (every
# remaining pair's parent is unbuilt) (gist §3.2)
law fit_reaches_budget:
  for +m: O.Age
  for +t: List<&2, Bool>
  for +budget: Nat
  for +ph: Nat
  for +info: O.Info
  for +v: List<&2, O.Node>
  Or({Nat.is_le(O.view_size(ph, info, O.fit.view(m, t, budget, ph, info, v)), budget) == True{} : Bool}, {S.can_merge(info, O.fit.view(m, t, budget, ph, info, v)) == False{} : Bool})

# LAW: a fit merges only into built parents
law fit_merges_built:
  for +m: O.Age
  for +t: List<&2, Bool>
  for +budget: Nat
  for +ph: Nat
  for +info: O.Info
  for +v: List<&2, O.Node>
  S.Built(info, Pair.fst(List<&2, O.Node>, List<&2, O.Node>, O.fit(m, t, budget, ph, info, v)))

# LAW: after any history, every merged line of the view is built: only
# a message's own line may still wait for its summary (gist §3)
law view_summarized:
  for +cfg: O.Cfg
  for +evs: List<&2, O.Ev>
  S.Summarized(O.St.info(O.run(cfg, evs)), S.view.of(cfg, evs))

# LAW: so is every merged line of the compaction view
law cview_summarized:
  for +cfg: O.Cfg
  for +evs: List<&2, O.Ev>
  S.Summarized(O.St.info(O.run(cfg, evs)), S.cview.of(cfg, evs))

# (f) First is not last
# ---------------------
# At T = 10, with the view 0+4, 4+4, 8+1, 9+1 and a budget of 3 lines
# (gist §3.2):

# LAW: due from the pair's last message merges 8-9, as push does
law last_merges_8_9:
  {O.fit.view(O.Last{}, S.ten(), 3n, 0n, O.All{1n}, S.view10()) == [O.Node{2n, []}, O.Node{2n, [True{}]}, O.Node{1n, [False{}, False{}, True{}]}] : List<&2, O.Node>}

# LAW: due from its first message merges 0-7 instead
law first_merges_0_7:
  {O.fit.view(O.First{}, S.ten(), 3n, 0n, O.All{1n}, S.view10()) == [O.Node{3n, []}, O.Node{0n, [False{}, False{}, False{}, True{}]}, O.Node{0n, [True{}, False{}, False{}, True{}]}] : List<&2, O.Node>}

# LAW: so the two measures are not the same
law first_is_not_last:
  {O.fit.view(O.First{}, S.ten(), 3n, 0n, O.All{1n}, S.view10()) != O.fit.view(O.Last{}, S.ten(), 3n, 0n, O.All{1n}, S.view10()) : List<&2, O.Node>}

# LAW: and from the first message the view leaves push within 11 steps
law first_leaves_push:
  {O.agree(O.First{}, 11n) == False{} : Bool}

# (g) A compaction's view
# -----------------------

# LAW: a compaction's view ends at its node (before the message, or by
# the merge's last message) and holds only built lines (gist §4)
law context_ends_at_node:
  for +s: O.St
  for +n: O.Node
  S.Before(O.St.info(s), O.ctx.bound(n), O.ctx(s, n))

# LAW: it is the start of the compaction view, so compactions share
# their cache prefix (gist §4)
law context_is_prefix:
  for +s: O.St
  for +n: O.Node
  S.Prefix(O.ctx(s, n), O.St.cview(s))
