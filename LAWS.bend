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
import ./bend/compactor.bend as C
import ./bend/wait.bend as Wt
import ./bend/lease.bend as Ls
import ./bend/child.bend as Ch
import ./bend/run.bend as Rn
import ./bend/admission.bend as Ad
import ./bend/tree.bend as Tr

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

# LAW: and at every step t of any number n of pushes: after each push the
# view and push's list hold the same lines (gist §3.2, for all t)
law push_agrees_always:
  for n: Nat
  {O.agree(O.Last{}, n) == True{} : Bool}

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

# (H1) A compactor call always ends with a line that fits
# -------------------------------------------------------
# docs/harness.md H1, the model in bend/compactor.bend. A reply is free:
# any text, empty, thinking only, an error, missing.

# LAW: a line makes at most `tries` model calls
law line_calls_at_most_tries:
  for +tries: Nat
  for +node: Nat
  for +input: List<&2, C.W>
  for rs: List<&2, C.Reply>
  {Nat.is_le(C.Line.calls(C.line(tries, node, input, rs)), tries) == True{} : Bool}

# LAW: with an input that is not empty and a node of at least 4 bytes
# (a character's widest), the line has 1 to node bytes, or the call failed
law line_fits:
  for +tries: Nat
  for +k: Nat
  for +c: C.W
  for +rest: List<&2, C.W>
  for +rs: List<&2, C.Reply>
  {C.line.fits(4n+k, C.Line.line(C.line(tries, 4n+k, c <> rest, rs))) == True{} : Bool}

# LAW: when a reply the line read fits, the line is the first such reply
law line_takes_first_fit:
  for +tries: Nat
  for +node: Nat
  for +input: List<&2, C.W>
  for +rs: List<&2, C.Reply>
  {C.line.first(C.first_fit(node, C.read(C.Line.calls(C.line(tries, node, input, rs)), rs)), C.Line.line(C.line(tries, node, input, rs))) == True{} : Bool}

# LAW: a follow-up not shorter than the best reply ends the line: the
# best reply, cut to node bytes, after 2 calls
law line_stops_when_not_shorter:
  for +t: Nat
  for +node: Nat
  for +input: List<&2, C.W>
  for +a: List<&2, C.W>
  for +b: List<&2, C.W>
  for +rest: List<&2, C.Reply>
  for +over: {Nat.is_lt(node, C.Text.len(a)) == True{} : Bool}
  for +longer: {Nat.is_le(C.Text.len(a), C.Text.len(b)) == True{} : Bool}
  {C.line(2n+t, node, input, C.Says{a} <> C.Says{b} <> rest) == C.Line{2n, Some{C.cut(a, node)}} : C.Line}

# LAW: an empty (or thinking-only) reply is a try, not a failure: the
# line is the input cut to node bytes
law line_empty_is_a_try:
  for t: Nat
  for node: Nat
  for input: List<&2, C.W>
  for rest: List<&2, C.Reply>
  {C.line(1n+t, node, input, C.Says{Nil{}} <> rest) == C.Line{1n, Some{C.cut(input, node)}} : C.Line}

# LAW: a provider error fails the call
law line_error_fails:
  for t: Nat
  for node: Nat
  for input: List<&2, C.W>
  for rest: List<&2, C.Reply>
  {C.line(1n+t, node, input, C.Erred{} <> rest) == C.Line{1n, None{}} : C.Line}

# LAW: a line with n failures left is built once n+1 of its calls failed,
# whatever came between them (disk errors, stops, a saved line)
law fail_cap_builds:
  for n: Nat
  for os: List<&2, C.Outcome>
  for many: {Nat.is_le(1n+n, C.failures(os)) == True{} : Bool}
  {C.Pend.run(os, C.Owed{n}) == C.Made{} : C.Pend}

# (H2) A turn never waits forever for the memory
# ----------------------------------------------
# docs/harness.md H2: the need-first queue of bend/optchat.bend, the settle
# of bend/compactor.bend.

# LAW: while a turn waits, every node the queue starts is a line of the
# view that is not built
law need_first:
  for +cfg: O.Cfg
  for +s: O.St
  {C.needed(O.St.info(s), O.St.view(s), O.cands.need(cfg, s)) == True{} : Bool}

# LAW: when a turn starts to wait, every call it does not need stops
# (O.St.wait): then every running call and every call the queue starts
# is for a line of the view that is not built
law need_first_running:
  for +cfg: O.Cfg
  for +s: O.St
  {C.needed(O.St.info(s), O.St.view(s), List.append(&2, O.Node, O.St.busy(O.St.wait(s)), O.cands.need(cfg, O.St.wait(s)))) == True{} : Bool}

# LAW: and it stops no call the view needs: a call of a view line not
# built still runs. Every waiting turn waits for the same view, so no
# turn's wait stops a call another waiting turn needs.
law wait_keeps_needed:
  for +s: O.St
  {C.kept(O.St.info(s), O.St.view(s), O.St.busy(s), O.St.busy(O.St.wait(s))) == True{} : Bool}

# LAW: the queue never stalls a waiting turn: after any events, while
# fewer than jobs calls run and a view line is neither built nor busy,
# the queue starts a node
law need_progress:
  for +cfg: O.Cfg
  for +evs: List<&2, O.Ev>
  for room: {Nat.is_lt(List.length(&2, O.Node, O.St.busy(O.run(cfg, evs))), O.Cfg.jobs(cfg)) == True{} : Bool}
  for idle: {C.idle(O.St.info(O.run(cfg, evs)), O.St.view(O.run(cfg, evs)), O.St.busy(O.run(cfg, evs))) == True{} : Bool}
  {O.Nat.is_pos(List.length(&2, O.Node, O.cands.need(cfg, O.run(cfg, evs)))) == True{} : Bool}

# LAW: each outcome that counts (a saved line, a failed call) of a
# pending line's call lowers the measure
law settle_falls:
  for +ps: List<&2, C.Pend>
  for +k: Nat
  for +o: C.Outcome
  for due: {C.pending_at(ps, k) == True{} : Bool}
  for lands: {C.Outcome.lands(o) == True{} : Bool}
  {Nat.is_lt(C.measure(C.hit(ps, k, o)), C.measure(ps)) == True{} : Bool}

# LAW: after any outcomes, disk errors and stops among them, those that
# counted for a pending line plus the measure left are at most the
# measure at the start
law settle_bounded:
  for +es: List<&2, C.End>
  for +ps: List<&2, C.Pend>
  {Nat.is_le(Nat.add(C.hits(es, ps), C.measure(C.run(es, ps))), C.measure(ps)) == True{} : Bool}

# LAW: so once as many outcomes as the measure counted for pending lines,
# every line of the view is built
law settle_reached:
  for +es: List<&2, C.End>
  for +ps: List<&2, C.Pend>
  for enough: {Nat.is_le(C.measure(ps), C.hits(es, ps)) == True{} : Bool}
  {C.settled(C.run(es, ps)) == True{} : Bool}

# LAW: when a turn starts to wait, the measure is the failure cap (1+p)
# times the view's unbuilt lines
law settle_start:
  for +p: Nat
  for +info: O.Info
  for +v: List<&2, O.Node>
  {C.measure(C.settle.start(p, info, v)) == Nat.mul(C.unbuilt(info, v), 1n+p) : Nat}

# (H6) Every other wait has an exit
# ---------------------------------
# docs/harness.md H6. A wait (bend/wait.bend) sees, one at a time and in
# any order, its event, ticks of time, and the cancel; dl is its deadline
# in ticks (None: none). The root-turn lease (bend/lease.bend) takes any
# sequence of asks, releases, stops and crashes.

# LAW: a wait ends exactly once when its event, its cancel or its
# deadline comes, and never otherwise
law wait_ends_once:
  for +dl: Maybe<&2, Nat>
  for +xs: List<&2, Wt.Sig>
  {List.length(&2, Wt.End, Wt.run(dl, xs)) == Wt.once(Wt.exits(dl, xs)) : Nat}

# LAW: once the cancel or the deadline came, the wait's end is final:
# what comes after changes nothing
law wait_end_is_final:
  for +dl: Maybe<&2, Nat>
  for +pre: List<&2, Wt.Sig>
  for +post: List<&2, Wt.Sig>
  for stop: {Wt.stops(dl, pre) == True{} : Bool}
  {Wt.run(dl, List.append(&2, Wt.Sig, pre, post)) == Wt.run(dl, pre) : List<&2, Wt.End>}

# LAW: an event that comes before the cancel and the deadline ends the
# wait with the event
law wait_arrival_wins:
  for +dl: Maybe<&2, Nat>
  for +pre: List<&2, Wt.Sig>
  for +post: List<&2, Wt.Sig>
  for calm: {Wt.exits(dl, pre) == False{} : Bool}
  {Wt.run(dl, List.append(&2, Wt.Sig, pre, Wt.Arrive{} <> post)) == [Wt.Arrived{}] : List<&2, Wt.End>}

# LAW: a cancel that comes before the event and the deadline ends the
# wait as cancelled
law wait_cancel_wins:
  for +dl: Maybe<&2, Nat>
  for +pre: List<&2, Wt.Sig>
  for +post: List<&2, Wt.Sig>
  for calm: {Wt.exits(dl, pre) == False{} : Bool}
  {Wt.run(dl, List.append(&2, Wt.Sig, pre, Wt.Cancel{} <> post)) == [Wt.Cancelled{}] : List<&2, Wt.End>}

# LAW: first come, first served: after any events, the holder asked
# before every waiter, and the waiters wait in the order they asked
law lease_fifo:
  for +evs: List<&2, Ls.Ev>
  Ls.Fifo(Ls.run(evs))

# LAW: after any events, the lease is held or no live waiter waits: a
# release or a crash hands it to the next waiter at once
law lease_never_idle:
  for +evs: List<&2, Ls.Ev>
  Ls.Busy(Ls.run(evs))

# LAW: in any state, an event that does not end a live waiter (its
# release, its stop, its origin's crash) leaves it waiting or holding
law lease_keeps_waiters:
  for +s: Ls.L
  for +e: Ls.Ev
  for +k: Nat
  for +o: Nat
  for waits: Ls.In(Ls.Waiter{k, o, True{}}, Ls.L.queue(s))
  for other: {Ls.hits(e, Ls.Waiter{k, o, True{}}) == False{} : Bool}
  Ls.Kept(k, o, Ls.step(s, e))

# LAW: a waiter that stopped waiting never holds the lease, whatever
# comes after
law lease_stop_never_holds:
  for +evs: List<&2, Ls.Ev>
  for +k: Nat
  for +o: Nat
  for +rest: List<&2, Ls.Ev>
  for waits: Ls.In(Ls.Waiter{k, o, True{}}, Ls.L.queue(Ls.run(evs)))
  Ls.NotHeld(k, Ls.L.holder(Ls.go(rest, Ls.step(Ls.run(evs), Ls.Stop{k}))))

# LAW: in any state, a crash ends every lease of its origin, held or
# waited for
law lease_crash_frees:
  for +s: Ls.L
  for +p: Nat
  Ls.Freed(p, Ls.step(s, Ls.Crash{p}))

# (H5) Every subagent reports back exactly once
# ---------------------------------------------
# bend/child.bend: the parent's task on one child. The watch's clock
# counts down the ms of no progress left (`left`, full: subagentStallMs)
# and the failed polls in a row left (`tries`, full: CHILD_POLL_FAILURES).

# LAW: quiet polls (the child unsettled with the token the watch holds,
# or a failed poll), at least as many as the ms left on the clock, end the
# watch: each poll takes 1 ms or more
law child_stalls_in_time:
  for +cfg: Ch.Cfg
  for +w: Ch.W
  for +h: Ch.Hush
  for +hs: List<&2, Ch.Hush>
  for long: {Nat.is_le(Ch.W.left(w), List.length(&2, Ch.Hush, h <> hs)) == True{} : Bool}
  {Ch.Next.watching(Ch.hush(h <> hs, cfg, Ch.Watch{w})) == False{} : Bool}

# LAW: failed polls in a row, as many as the tries left, end the watch
law child_unreachable_in_time:
  for +cfg: Ch.Cfg
  for +w: Ch.W
  for +d: Nat
  for +ds: List<&2, Nat>
  for long: {Nat.is_le(Ch.W.tries(w), List.length(&2, Nat, d <> ds)) == True{} : Bool}
  {Ch.Next.watching(Ch.hush(Ch.misses(d <> ds), cfg, Ch.Watch{w})) == False{} : Bool}

# LAW: whatever a poll reads, the clock stays at most full: the bounds
# above are at most subagentStallMs and CHILD_POLL_FAILURES polls
law child_clock_bounded:
  for +cfg: Ch.Cfg
  for +w: Ch.W
  for +e: Nat
  for +o: Ch.Obs
  for full: {Ch.within(cfg, Ch.Watch{w}) == True{} : Bool}
  {Ch.within(cfg, Ch.look(cfg, w, e, o)) == True{} : Bool}

# LAW: a poll that reads a new token (progress) is never a stall: the
# watch goes on with a full clock
law child_progress_is_not_a_stall:
  for +cfg: Ch.Cfg
  for +w: Ch.W
  for +e: Nat
  for +x: Nat
  for news: {Ch.moved(Ch.W.tok(w), Some{x}) == True{} : Bool}
  {Ch.look(cfg, w, e, Ch.Busy{Some{x}}) == Ch.Watch{Ch.W.fresh(cfg, Some{x})} : Ch.Next}

# The report laws hold after any events: task steps (polls), the parent's
# deliveries and withdrawals of any submission id, its aborts, closes and
# reopens, and task aborts and deletes, in any order. The parent's inbox
# keeps every submission of the report, each queued, withdrawn or placed.

# LAW: at most one submission of the report is live (queued or placed):
# the task submits again only once its last submission is withdrawn, so
# no two ids of the report can both reach the transcript
law child_one_live:
  for +cfg: Ch.Cfg
  for +evs: List<&2, Ch.Ev>
  {Nat.is_le(Ch.live(Ch.St.inbox(Ch.run(evs, cfg, Ch.St.init(cfg)))), 1n) == True{} : Bool}

# LAW: at most one submission of the report is placed: the parent's
# transcript holds the report at most once
law child_report_once:
  for +cfg: Ch.Cfg
  for +evs: List<&2, Ch.Ev>
  {Nat.is_le(Ch.St.placed(Ch.run(evs, cfg, Ch.St.init(cfg))), 1n) == True{} : Bool}

# LAW: the report is submitted at most once more than the parent withdrew
# (an abort, a close, a withdrawal of one input): a resubmission follows a
# withdrawal
law child_resubmits_per_abort:
  for +cfg: Ch.Cfg
  for +evs: List<&2, Ch.Ev>
  {Nat.is_le(List.length(&2, Ch.Sub, Ch.St.inbox(Ch.run(evs, cfg, Ch.St.init(cfg)))), Nat.add(Ch.cuts(evs), 1n)) == True{} : Bool}

# LAW: a report the task owes is placed exactly once when the parent
# reopens, the task takes three steps (the first may run a pending abort)
# and the parent's run places the submission the task then waits on (its
# owed id m): the report is never lost
law child_delivered_once:
  for +cfg: Ch.Cfg
  for +evs: List<&2, Ch.Ev>
  for +d1: Nat
  for +o1: Ch.Obs
  for +d2: Nat
  for +o2: Ch.Obs
  for +d3: Nat
  for +o3: Ch.Obs
  for owing: {Ch.Ph.owing(Ch.St.ph(Ch.run(evs, cfg, Ch.St.init(cfg)))) == True{} : Bool}
  for +m: Nat
  for waits: {Ch.St.owed(Ch.run([Ch.Reopen{}, Ch.Poll{d1, o1}, Ch.Poll{d2, o2}, Ch.Poll{d3, o3}], cfg, Ch.run(evs, cfg, Ch.St.init(cfg)))) == m : Nat}
  {Ch.St.placed(Ch.run([Ch.Reopen{}, Ch.Poll{d1, o1}, Ch.Poll{d2, o2}, Ch.Poll{d3, o3}, Ch.Deliver{m}], cfg, Ch.run(evs, cfg, Ch.St.init(cfg)))) == 1n : Nat}

# (H4) Every run ends
# -------------------
# docs/harness.md H4, the model in bend/run.bend: one run (one user turn)
# through prepare, call (a request or a deferred poll), compact (an
# overflow's or a blocking threshold one) and tools. Every input is free:
# any model reply, any round hash and end, any compaction result, an
# abort, in any order.

# LAW: every run has ended (answered, aborted or failed) after bound(cfg)
# inputs, whatever they are and whatever follows them; bound(cfg) =
# max(cap, 1)·(2 + (retries + 2)·(polls + 2)), from maxToolRounds,
# MAX_POLLS, retry.maxRetries and one compaction a generation
law run_ends:
  for +cfg: Rn.Cfg
  for +evs: List<&2, Rn.Ev>
  for long: {List.length(&2, Rn.Ev, evs) == Rn.bound(cfg) : Nat}
  for +more: List<&2, Rn.Ev>
  {Rn.done(Rn.run(cfg, List.append(&2, Rn.Ev, evs, more))) == True{} : Bool}

# LAW: an ended run stays as it ended
law run_end_stays:
  for +cfg: Rn.Cfg
  for +s: Rn.St
  for ended: {Rn.done(s) == True{} : Bool}
  for +e: Rn.Ev
  {Rn.step(cfg, s, e) == s : Rn.St}

# LAW: an abort ends a live run as aborted, at the next step
law run_abort_ends_now:
  for +cfg: Rn.Cfg
  for +s: Rn.St
  for live: {Rn.done(s) == False{} : Bool}
  {Rn.St.ph(Rn.step(cfg, s, Rn.Abort{})) == Rn.Aborted{} : Rn.Ph}

# LAW: a run that has made max(cap, 1) tool rounds has failed
law run_rounds_capped:
  for +cfg: Rn.Cfg
  for +evs: List<&2, Rn.Ev>
  Or({Rn.failed(Rn.run(cfg, evs)) == True{} : Bool}, {Nat.is_lt(List.length(&2, Nat, Rn.hist(cfg, evs)), Nat.max(Rn.Cfg.cap(cfg), 1n)) == True{} : Bool})

# LAW: the loop guard fails a run only when its last `loop` rounds made the
# same calls with the same results: a run whose results change is no loop
law run_loop_needs_repeats:
  for +cfg: Rn.Cfg
  for +evs: List<&2, Rn.Ev>
  Or({Rn.looped(Rn.run(cfg, evs)) == False{} : Bool}, {Rn.rep(Rn.Cfg.loop(cfg), Rn.hist(cfg, evs)) == True{} : Bool})

# LAW: the round cap fails a run only at its max(cap, 1)th round, never
# earlier
law run_rounds_fail_at_cap:
  for +cfg: Rn.Cfg
  for +evs: List<&2, Rn.Ev>
  Or({Rn.capped(Rn.run(cfg, evs)) == False{} : Bool}, {List.length(&2, Nat, Rn.hist(cfg, evs)) == Nat.max(Rn.Cfg.cap(cfg), 1n) : Nat})

# LAW: the poll cap fails a run only when its request's reply and each of
# its `polls` polls were deferred, polls + 1 deferred replies in a row
law run_polls_need_defers:
  for +cfg: Rn.Cfg
  for +evs: List<&2, Rn.Ev>
  Or({Rn.polled(Rn.run(cfg, evs)) == False{} : Bool}, {Rn.defers(cfg, evs) == 1n+Rn.Cfg.polls(cfg) : Nat})

# (H3) A user's request never waits behind background work
# ---------------------------------------------------------
# docs/harness.md H3, the model in bend/admission.bend: one provider's
# admission (crates/eukhe-core/src/admission.rs), ticket by ticket. Every
# op is free: admits of either class, polls, drops of permits and of
# waiters, new limits, in any order, on any state.

# LAW: an interactive admit leaves no background slot held (H3.1)
law admission_preempts:
  for +s: Ad.St
  {Ad.cnt(Ad.Holding{}, Ad.Bg{}, Ad.St.ts(Ad.step(s, Ad.Admit{Ad.Ia{}}))) == 0n : Nat}

# LAW: an op grants only into free slots: after it the slots held are
# within the limit, or no more than before less the slots the op freed
# itself (a lowered limit drains, and nothing is granted until below it)
law admission_capacity:
  for +s: Ad.St
  for +o: Ad.Op
  {Bool.or(Ad.within(Ad.St.lim(Ad.step(s, o)), Ad.held(Ad.St.ts(Ad.step(s, o)))), Ad.le(Nat.add(Ad.held(Ad.St.ts(Ad.step(s, o))), Ad.freed(s, o)), Ad.held(Ad.St.ts(s)))) == True{} : Bool}

# LAW: after any history no waiter may take a free slot: no free slot
# while an interactive request waits, or a background one waits with no
# interactive request holding or waiting (H3.3)
law admission_no_lost_wakeup:
  for +l: Ad.Lim
  for +q: Nat
  for +os: List<&2, Ad.Op>
  {Ad.grantable(Ad.run(os, Ad.St.new(l, q))) == False{} : Bool}

# LAW: after any history a background slot is held only while no
# interactive request holds a slot or waits (H3.1)
law admission_background_yields:
  for +l: Ad.Lim
  for +q: Nat
  for +os: List<&2, Ad.Op>
  {Ad.calm(Ad.St.ts(Ad.run(os, Ad.St.new(l, q)))) == True{} : Bool}

# LAW: after any history no request holds a slot while an older one of
# its class waits: grants within a class go oldest first (H3.2)
law admission_fifo:
  for +l: Ad.Lim
  for +q: Nat
  for +os: List<&2, Ad.Op>
  {Ad.fifo.both(Ad.St.ts(Ad.run(os, Ad.St.new(l, q)))) == True{} : Bool}

# LAW: while interactive ticket w waits, no op raises what it waits for
# (the interactive slots held and the interactive waiters ahead of it),
# and each interactive slot an op frees lowers it (H3.4)
law admission_interactive_step:
  for +s: Ad.St
  for +o: Ad.Op
  for +w: Nat
  for ws: {Ad.waits.ia(Ad.status(s, w)) == True{} : Bool}
  for wf: {Ad.waits.ia(Ad.status(Ad.step(s, o), w)) == True{} : Bool}
  {Ad.le(Nat.add(Ad.frees(s, o), Ad.ahead(Ad.step(s, o), w)), Ad.ahead(s, w)) == True{} : Bool}

# LAW: so an interactive waiter w is granted after at most ahead(s, w)
# interactive releases, whatever background requests do: while it keeps
# waiting through a run, the run freed fewer interactive slots (H3.4)
law admission_interactive_bound:
  for +l: Ad.Lim
  for +q: Nat
  for +pre: List<&2, Ad.Op>
  for +os: List<&2, Ad.Op>
  for +w: Nat
  for waits: {Ad.waits.thru(os, Ad.run(pre, Ad.St.new(l, q)), w) == True{} : Bool}
  {Ad.le(1n+Ad.frees.run(os, Ad.run(pre, Ad.St.new(l, q))), Ad.ahead(Ad.run(pre, Ad.St.new(l, q)), w)) == True{} : Bool}

# LAW: an ended ticket stays ended, whatever op comes
law admission_ended_stays_ended:
  for +s: Ad.St
  for +o: Ad.Op
  for +k: Nat
  for e: {Ad.ended(Ad.status(s, k)) == True{} : Bool}
  {Ad.ended(Ad.status(Ad.step(s, o), k)) == True{} : Bool}

# LAW: ending an ended ticket again changes nothing: no double release
law admission_end_twice_changes_nothing:
  for +s: Ad.St
  for +k: Nat
  for e: {Ad.ended(Ad.status(s, k)) == True{} : Bool}
  {Ad.step(s, Ad.finish(Ad.status(s, k), k)) == s : Ad.St}

# LAW: every ticket ends when its holder drops it (a waiter leaves, a
# permit is released): no leak
law admission_every_ticket_ends:
  for +s: Ad.St
  for +k: Nat
  for live: {Maybe.is_some(&2, Ad.Tk, Ad.status(s, k)) == True{} : Bool}
  {Ad.ended(Ad.status(Ad.step(s, Ad.finish(Ad.status(s, k), k)), k)) == True{} : Bool}

# (S1) The session tree
# ---------------------
# docs/harness.md S1, the model in bend/tree.bend. One tree holds the
# state of a session; the journal is its list of records. Every record
# is free: any put (valid or not), any delete, any rewind ops.

# LAW: a record keeps a valid tree valid: keys in order, and every node
# under the root or under a node (no orphan, no cycle)
law tree_apply_sound:
  for +t: List<&2, Tr.Ent>
  for good: {Tr.sound(t) == True{} : Bool}
  for r: Tr.Rec
  {Tr.sound(Tr.apply(t, r)) == True{} : Bool}

# LAW: so every journal makes a valid tree
law tree_replay_sound:
  for rs: List<&2, Tr.Rec>
  {Tr.sound(Tr.replay(rs)) == True{} : Bool}

# LAW: a snapshot after any prefix of the journal, with the records after
# it, makes the tree of the whole journal. So a client that holds a
# snapshot and gets the records after it holds the live tree.
law tree_snapshot:
  for +pre: List<&2, Tr.Rec>
  for post: List<&2, Tr.Rec>
  {Tr.go(post, Tr.replay(pre)) == Tr.replay(List.append(&2, Tr.Rec, pre, post)) : List<&2, Tr.Ent>}

# LAW: a rewind with diff(current, target) makes the target, exactly
law tree_rewind_reaches:
  for +a: List<&2, Tr.Ent>
  for +b: List<&2, Tr.Ent>
  for ga: {Tr.sound(a) == True{} : Bool}
  for gb: {Tr.sound(b) == True{} : Bool}
  {Tr.apply(a, Tr.Rewind{Tr.diff(a, b)}) == b : List<&2, Tr.Ent>}

# LAW: a rewind to the current tree has no ops
law tree_rewind_still:
  for +a: List<&2, Tr.Ent>
  for ga: {Tr.sorted(a) == True{} : Bool}
  {Tr.diff(a, a) == Nil{} : List<&2, Tr.Op>}

# LAW: every op of a rewind is on a node that differs between the
# current tree and the target: a rewind starts, stops or restores only
# what changed
law tree_rewind_minimal:
  for +a: List<&2, Tr.Ent>
  for +b: List<&2, Tr.Ent>
  for ga: {Tr.sorted(a) == True{} : Bool}
  for gb: {Tr.sorted(b) == True{} : Bool}
  {Tr.changed(a, b, Tr.diff(a, b)) == True{} : Bool}

# LAW: a delete removes its node
law tree_delete_removes:
  for +t: List<&2, Tr.Ent>
  for good: {Tr.sound(t) == True{} : Bool}
  for +x: Nat
  {Tr.has(Tr.apply(t, Tr.Do{Tr.Del{x}}), x) == False{} : Bool}

# LAW: a delete removes a node only when it is the deleted node or its
# parent is removed: it removes the subtree, nothing else
law tree_delete_only_below:
  for +t: List<&2, Tr.Ent>
  for good: {Tr.sound(t) == True{} : Bool}
  for +x: Nat
  {Tr.only_below(t, x, Tr.apply(t, Tr.Do{Tr.Del{x}})) == True{} : Bool}

# LAW: a delete changes no node it keeps
law tree_delete_within:
  for +t: List<&2, Tr.Ent>
  for good: {Tr.sound(t) == True{} : Bool}
  for +x: Nat
  {Tr.within(Tr.apply(t, Tr.Do{Tr.Del{x}}), t) == True{} : Bool}

# LAW: a put under the root or a node sets its node
law tree_put_sets:
  for +t: List<&2, Tr.Ent>
  for good: {Tr.sound(t) == True{} : Bool}
  for +k: Nat
  for +p: Nat
  for +v: Nat
  for fits: {Tr.ok(t, k, p) == True{} : Bool}
  {Tr.get(Tr.apply(t, Tr.Do{Tr.Put{k, p, v}}), k) == Some{Tr.Ent{k, p, v}} : Maybe<&2, Tr.Ent>}

# LAW: a put changes no other node
law tree_put_keeps_others:
  for +t: List<&2, Tr.Ent>
  for good: {Tr.sound(t) == True{} : Bool}
  for +k: Nat
  for +p: Nat
  for +v: Nat
  for +x: Nat
  for other: {Nat.is_eq(x, k) == False{} : Bool}
  {Tr.get(Tr.apply(t, Tr.Do{Tr.Put{k, p, v}}), x) == Tr.get(t, x) : Maybe<&2, Tr.Ent>}
