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
import ./bend/job.bend as Jb
import ./bend/sandbox.bend as Sb
import ./bend/cvar.bend as Cv
import ./bend/director.bend as Dr
import ./bend/infer.bend as If
import ./bend/tools.bend as Tl
import ./bend/screen.bend as Sc
import ./bend/tiny.bend as Tn
import ./bend/effort.bend as Ef
import ./laws/release.bend as Release
import ./laws/auth_flight.bend as AuthFlight
import ./laws/themes.bend as Themes
import ./laws/dashboard_tokens.bend as DashTokens
import ./laws/progress.bend as Prg
import ./laws/ladder.bend as Ladder
import ./laws/kernel_local.bend as KernelLocal
import ./laws/storage.bend as Storage
import ./laws/recover.bend as Rec
import ./laws/catalog_union.bend as CatalogUnion
import ./laws/cron.bend as Cronl
import ./laws/supervisor.bend as Sup

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
# docs/state.md S1, the model in bend/tree.bend. One tree holds the
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

# (S2) Jobs and limits
# --------------------
# docs/runtime.md S2, the model in bend/job.bend. Every event is free:
# any output size, exit, kill or tick, in any order; any output cap or
# the opt-out; any budget; any tool call stream; any job table.

# LAW: with a cap, a job keeps at most cap bytes of its output
law job_output_bounded:
  for +c: Nat
  for es: List<&2, Jb.JEv>
  {Nat.is_le(Jb.J.kept(Jb.run(Some{c}, es)), c) == True{} : Bool}

# LAW: no output is lost in silence: the bytes kept plus the bytes
# counted as dropped are every byte the job wrote before it ended
law job_no_silent_loss:
  for +cap: Maybe<&2, Nat>
  for +es: List<&2, Jb.JEv>
  {Nat.add(Jb.J.kept(Jb.run(cap, es)), Jb.J.dropped(Jb.run(cap, es))) == Jb.produced(es) : Nat}

# LAW: with the opt-out, a job drops nothing
law job_optout_keeps_all:
  for es: List<&2, Jb.JEv>
  {Jb.J.dropped(Jb.run(None{}, es)) == 0n : Nat}

# LAW: a cap drops nothing from output that fits
law job_cap_drops_only_excess:
  for +c: Nat
  for +es: List<&2, Jb.JEv>
  for fits: {Nat.is_le(Jb.produced(es), c) == True{} : Bool}
  {Jb.J.dropped(Jb.run(Some{c}, es)) == 0n : Nat}

# LAW: a job reports exactly one end once it exits or is killed, and none
# before
law job_ends_once:
  for +cap: Maybe<&2, Nat>
  for +es: List<&2, Jb.JEv>
  {List.length(&2, Jb.End, Jb.ends(cap, es)) == Jb.once(Jb.has_end(es)) : Nat}

# LAW: an ended job stays as it ended: no late output, no second end
law job_end_is_final:
  for +cap: Maybe<&2, Nat>
  for +pre: List<&2, Jb.JEv>
  for post: List<&2, Jb.JEv>
  for ended: {Jb.has_end(pre) == True{} : Bool}
  {Jb.run(cap, List.append(&2, Jb.JEv, pre, post)) == Jb.run(cap, pre) : Jb.J}

# LAW: a kill ends a live job at once, as killed, with its output kept
law job_kill_ends_now:
  for +cap: Maybe<&2, Nat>
  for +k: Nat
  for +d: Nat
  {Jb.step(cap, Jb.Live{k, d}, Jb.Kill{}) == Jb.Ended{k, d, Jb.Killed{}} : Jb.J}

# LAW: a blocking call returns once its budget of ticks passed: it never
# blocks longer
law call_blocks_at_most_budget:
  for +b: Nat
  for +es: List<&2, Jb.JEv>
  for long: {Nat.is_le(b, Jb.ticks(es)) == True{} : Bool}
  {Maybe.is_some(&2, Jb.Wait, Jb.wait(es, b)) == True{} : Bool}

# LAW: a call that settles in time reports the job's own end, and the job
# has no other end
law call_settles_with_job:
  for +cap: Maybe<&2, Nat>
  for +b: Nat
  for +es: List<&2, Jb.JEv>
  for +x: Jb.End
  for settled: {Jb.wait(es, b) == Some{Jb.Settled{x}} : Maybe<&2, Jb.Wait>}
  {Jb.ends(cap, es) == [x] : List<&2, Jb.End>}

# LAW: a tool call journals at most two records: its start and one final
# record; no delta is journaled
law stream_journals_two:
  for es: List<&2, Jb.CEv>
  {Nat.is_le(List.length(&2, Jb.CRec, Jb.journal(es)), 2n) == True{} : Bool}

# LAW: a tool call settles exactly once when it ends (result or cancel),
# and not before
law stream_settles_once:
  for +es: List<&2, Jb.CEv>
  {Jb.settles(Jb.journal(es)) == Jb.once(Jb.c.ends(es)) : Nat}

# LAW: the final record carries everything the stream carried: every
# result byte, every warning, all usage
law stream_settle_carries_all:
  for +es: List<&2, Jb.CEv>
  for ended: {Jb.c.ends(es) == True{} : Bool}
  {Jb.carried(Jb.journal(es)) == Some{Jb.Tally{Jb.c.bytes(es), Jb.c.warns(es), Jb.c.usage(es)}} : Maybe<&2, Jb.Tally>}

# LAW: after a rewind, every running job is a job of the target tree: no
# orphan job runs on
law rewind_stops_orphans:
  for +js: List<&2, Jb.Slot>
  for +keep: List<&2, Nat>
  {Jb.running_in(Jb.rewind(js, keep), keep) == True{} : Bool}

# LAW: a rewind leaves every job of the target tree as it was
law rewind_keeps_target_jobs:
  for +js: List<&2, Jb.Slot>
  for +keep: List<&2, Nat>
  {Jb.kept(Jb.rewind(js, keep), js, keep) == True{} : Bool}

# (S3) The host and the sandbox
# -----------------------------
# docs/runtime.md S3, the model in bend/sandbox.bend. Every input is
# free: any frames of any length and kind, any limits, any workspaces of
# the parent, the base and the child.

# LAW: every frame gets exactly one reply, in order
law proto_one_reply_each:
  for +fs: List<&2, Sb.Frame>
  for +max: Nat
  for +allowed: List<&2, Nat>
  {Sb.reply.ids(Sb.Host.replies(Sb.serve(fs, max, allowed))) == Sb.frame.ids(fs) : List<&2, Nat>}

# LAW: the host runs only frames it accepts: within the size limit and of
# an allowed kind
law proto_runs_only_accepted:
  for +fs: List<&2, Sb.Frame>
  for +max: Nat
  for +allowed: List<&2, Nat>
  {Sb.all_ok(Sb.Host.ran(Sb.serve(fs, max, allowed)), max, allowed) == True{} : Bool}

# LAW: and it runs every frame it accepts
law proto_runs_every_accepted:
  for +fs: List<&2, Sb.Frame>
  for +max: Nat
  for +allowed: List<&2, Nat>
  {List.length(&2, Sb.Frame, Sb.Host.ran(Sb.serve(fs, max, allowed))) == Sb.oks(fs, max, allowed) : Nat}

# LAW: a frame over the size limit gets an error and runs nothing
law proto_rejects_oversize:
  for +i: Nat
  for +l: Nat
  for +k: Nat
  for +max: Nat
  for +allowed: List<&2, Nat>
  for over: {Nat.is_lt(max, l) == True{} : Bool}
  {Sb.serve([Sb.Frame{i, l, k}], max, allowed) == Sb.Host{[Sb.Err{i}], Nil{}} : Sb.Host}

# LAW: a path the child did not change keeps the parent's content
law cow_keeps_parent:
  for +ks: List<&2, Nat>
  for +par: List<&2, Sb.Doc>
  for +base: List<&2, Sb.Doc>
  for +child: List<&2, Sb.Doc>
  for +k: Nat
  for listed: {Sb.elem(ks, k) == True{} : Bool}
  for calm: {Sb.m.eq(Sb.read(child, k), Sb.read(base, k)) == True{} : Bool}
  {Sb.read(Sb.Back.ws(Sb.back(ks, par, base, child)), k) == Sb.read(par, k) : Maybe<&2, Nat>}

# LAW: a path only the child changed gets the child's content
law cow_takes_child:
  for +ks: List<&2, Nat>
  for +par: List<&2, Sb.Doc>
  for +base: List<&2, Sb.Doc>
  for +child: List<&2, Sb.Doc>
  for +k: Nat
  for listed: {Sb.elem(ks, k) == True{} : Bool}
  for moved: {Sb.m.eq(Sb.read(child, k), Sb.read(base, k)) == False{} : Bool}
  for still: {Sb.m.eq(Sb.read(par, k), Sb.read(base, k)) == True{} : Bool}
  {Sb.read(Sb.Back.ws(Sb.back(ks, par, base, child)), k) == Sb.read(child, k) : Maybe<&2, Nat>}

# LAW: a path both changed to different contents keeps the parent's
# content and is reported as a conflict: no change is lost in silence
law cow_conflict_reported:
  for +ks: List<&2, Nat>
  for +par: List<&2, Sb.Doc>
  for +base: List<&2, Sb.Doc>
  for +child: List<&2, Sb.Doc>
  for +k: Nat
  for listed: {Sb.elem(ks, k) == True{} : Bool}
  for moved: {Sb.m.eq(Sb.read(child, k), Sb.read(base, k)) == False{} : Bool}
  for also: {Sb.m.eq(Sb.read(par, k), Sb.read(base, k)) == False{} : Bool}
  for apart: {Sb.m.eq(Sb.read(par, k), Sb.read(child, k)) == False{} : Bool}
  {Bool.and(Sb.m.eq(Sb.read(Sb.Back.ws(Sb.back(ks, par, base, child)), k), Sb.read(par, k)), Sb.elem(Sb.Back.clashes(Sb.back(ks, par, base, child)), k)) == True{} : Bool}

# LAW: a conflict is real: both changed the path, to different contents
law cow_conflict_is_real:
  for +ks: List<&2, Nat>
  for +par: List<&2, Sb.Doc>
  for +base: List<&2, Sb.Doc>
  for +child: List<&2, Sb.Doc>
  for +k: Nat
  for clash: {Sb.elem(Sb.Back.clashes(Sb.back(ks, par, base, child)), k) == True{} : Bool}
  {Bool.or(Bool.or(Sb.m.eq(Sb.read(child, k), Sb.read(base, k)), Sb.m.eq(Sb.read(par, k), Sb.read(base, k))), Sb.m.eq(Sb.read(par, k), Sb.read(child, k))) == False{} : Bool}

# (S4) Settings as console variables
# ----------------------------------
# docs/control.md S4, the model in bend/cvar.bend. Every input is free:
# any declarations (duplicate ids, wrong defaults), any config.cfg, any
# family of agents with any profiles and sets (wrong types, Global cvars,
# undeclared ids), any alias table.

# LAW: the registry holds each id once: a second declaration is rejected
law cvar_registry_unique:
  for xs: List<&2, Cv.Decl>
  {Cv.unique(Cv.registry(xs)) == True{} : Bool}

# LAW: every declaration of the registry has a default of its type
law cvar_registry_typed:
  for xs: List<&2, Cv.Decl>
  {Cv.all_typed(Cv.registry(xs)) == True{} : Bool}

# LAW: every value has the type of its cvar, in every agent; an
# undeclared cvar has no value
law cvar_value_typed:
  for +xs: List<&2, Cv.Decl>
  for +cfg: List<&2, Cv.Bind>
  for +fam: List<&2, Cv.Ag>
  for +x: Nat
  {Cv.typed.at(Cv.find(Cv.registry(xs), x), Cv.value(Cv.registry(xs), cfg, fam, x)) == True{} : Bool}

# LAW: a subagent with no profile and no sets has its parent's values
law cvar_inherits:
  for +ds: List<&2, Cv.Decl>
  for +cfg: List<&2, Cv.Bind>
  for +fam: List<&2, Cv.Ag>
  for +x: Nat
  {Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [Cv.Ag{Nil{}, Nil{}}]), x) == Cv.value(ds, cfg, fam, x) : Maybe<&2, Cv.Val>}

# LAW: a subagent's last valid set wins over its parent's value
law cvar_set_wins:
  for +ds: List<&2, Cv.Decl>
  for +cfg: List<&2, Cv.Bind>
  for +fam: List<&2, Cv.Ag>
  for +p: List<&2, Cv.Bind>
  for +ss: List<&2, Cv.Bind>
  for +x: Nat
  for +v: Cv.Val
  for ok: {Cv.valid(ds, Cv.Agent{}, Cv.Bind{x, v}) == True{} : Bool}
  {Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [Cv.Ag{p, List.append(&2, Cv.Bind, ss, [Cv.Bind{x, v}])}]), x) == Some{v} : Maybe<&2, Cv.Val>}

# LAW: a Global cvar has one value in every agent of every family: the
# value of config.cfg on the default; no profile or set changes it
law cvar_global_uniform:
  for +ds: List<&2, Cv.Decl>
  for +cfg: List<&2, Cv.Bind>
  for +fam: List<&2, Cv.Ag>
  for +x: Nat
  for +d: Cv.Decl
  for found: {Cv.find(ds, x) == Some{d} : Maybe<&2, Cv.Decl>}
  for global: {Cv.Decl.local(d) == False{} : Bool}
  {Cv.value(ds, cfg, fam, x) == Some{Cv.root.val(ds, cfg, x, d)} : Maybe<&2, Cv.Val>}

# LAW: an agent writes to its cfg only cvars that persist, and replicates
# only cvars that replicate
law cvar_written_flagged:
  for ss: List<&2, Cv.Bind>
  for +ds: List<&2, Cv.Decl>
  for +f: Cv.Flag
  {Cv.all_flag(Cv.written(ss, ds, f), ds, f) == True{} : Bool}

# LAW: the cfg an agent writes, read back as its profile, gives the same
# value of every cvar that persists
law cvar_persist_roundtrip:
  for +ds: List<&2, Cv.Decl>
  for +cfg: List<&2, Cv.Bind>
  for +ss: List<&2, Cv.Bind>
  for +x: Nat
  for keeps: {Cv.flag.at(Cv.find(ds, x), Cv.Persist{}) == True{} : Bool}
  {Cv.value(ds, cfg, [Cv.Ag{Cv.written(ss, ds, Cv.Persist{}), Nil{}}], x) == Cv.value(ds, cfg, [Cv.Ag{Nil{}, ss}], x) : Maybe<&2, Cv.Val>}

# LAW: a toggle twice, in any agent of any family, gives back the value
law cvar_toggle_twice:
  for +ds: List<&2, Cv.Decl>
  for +cfg: List<&2, Cv.Bind>
  for +fam: List<&2, Cv.Ag>
  for +a: Cv.Ag
  for +x: Nat
  {Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [Cv.toggle(ds, cfg, fam, Cv.toggle(ds, cfg, fam, a, x), x)]), x) == Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [a]), x) : Maybe<&2, Cv.Val>}

# LAW: an expansion leaves no alias to run: every alias is expanded, or
# the expansion reports a cycle or an unknown alias
law alias_expands_fully:
  for cs: List<&2, Cv.Cmd>
  for +as: List<&2, Cv.Alias>
  {Cv.Exp.plain(Cv.expand(cs, as)) == True{} : Bool}

# LAW: an alias that runs itself is a cycle, not an endless expansion
law alias_self_cycle:
  for +n: Nat
  for +as: List<&2, Cv.Alias>
  {Cv.expand([Cv.CRun{n}], Cv.Alias{n, [Cv.CRun{n}]} <> as) == Cv.Cycle{} : Cv.Exp}

# LAW: a run of an alias that does not exist is reported
law alias_unknown_reported:
  for +n: Nat
  for +as: List<&2, Cv.Alias>
  for gone: {Cv.body(as, n) == [Cv.CGone{n}] : List<&2, Cv.Cmd>}
  {Cv.expand([Cv.CRun{n}], as) == Cv.Unknown{} : Cv.Exp}

# LAW: an alias with plain commands runs exactly its commands
law alias_runs_body:
  for +n: Nat
  for +b: List<&2, Cv.Cmd>
  for +as: List<&2, Cv.Alias>
  for flat: {Cv.plain(b) == True{} : Bool}
  {Cv.expand([Cv.CRun{n}], Cv.Alias{n, b} <> as) == Cv.Flat{b} : Cv.Exp}

# LAW: a key press runs only plain commands: every alias it names is
# expanded, or the press reports a cycle or an unknown alias
law bind_press_plain:
  for +bs: List<&2, Cv.KeyBind>
  for +k: Nat
  for +as: List<&2, Cv.Alias>
  {Cv.Exp.plain(Cv.press(bs, k, as)) == True{} : Bool}

# LAW: a key with no bind runs nothing
law bind_unbound_runs_nothing:
  for +bs: List<&2, Cv.KeyBind>
  for +k: Nat
  for +as: List<&2, Cv.Alias>
  for free: {Cv.bound(bs, k) == Nil{} : List<&2, Cv.Cmd>}
  {Cv.press(bs, k, as) == Cv.Flat{Nil{}} : Cv.Exp}

# LAW: a press of a key runs the commands of its first bind
law bind_first_wins:
  for +k: Nat
  for +c: List<&2, Cv.Cmd>
  for +rest: List<&2, Cv.KeyBind>
  for +as: List<&2, Cv.Alias>
  {Cv.press(Cv.KeyBind{k, c} <> rest, k, as) == Cv.expand(c, as) : Cv.Exp}

# (S5) The Director stack
# -----------------------
# docs/control.md S5, the model in bend/director.bend. Every verdict is
# free: each layer of each step says what the adversary picks.

# LAW: a decision never grows the stack past its cap
law dir_stack_bounded:
  for +s: List<&2, Dr.Layer>
  for vs: List<&2, Dr.Verdict>
  for +cap: Nat
  for fits: {Nat.is_le(List.length(&2, Dr.Layer, s), cap) == True{} : Bool}
  {Nat.is_le(List.length(&2, Dr.Layer, Dr.Dec.stack(Dr.decide(s, vs, cap))), cap) == True{} : Bool}

# LAW: so neither does the loop, whatever its steps
law dir_loop_stack_bounded:
  for vss: List<&2, List<&2, Dr.Verdict>>
  for +cap: Nat
  for +l: Dr.Loop
  for fits: {Nat.is_le(List.length(&2, Dr.Layer, Dr.Loop.stack(l)), cap) == True{} : Bool}
  {Nat.is_le(List.length(&2, Dr.Layer, Dr.Loop.stack(Dr.run(vss, cap, l))), cap) == True{} : Bool}

# LAW: the loop ends (hands back or fails) after at most n + 1 steps,
# with n its global budget, whatever every layer says: no Director keeps
# the loop going for ever
law dir_loop_ends:
  for +n: Nat
  for +s: List<&2, Dr.Layer>
  for +vss: List<&2, List<&2, Dr.Verdict>>
  for +cap: Nat
  for long: {List.length(&2, List<&2, Dr.Verdict>, vss) == 1n+n : Nat}
  {Dr.ended(Dr.run(vss, cap, Dr.Loop{n, s, None{}})) == True{} : Bool}

# LAW: an ended loop stays as it ended
law dir_end_is_final:
  for +cap: Nat
  for +l: Dr.Loop
  for done: {Dr.ended(l) == True{} : Bool}
  for vs: List<&2, Dr.Verdict>
  {Dr.tick(cap, l, vs) == l : Dr.Loop}

# LAW: the stack in the tree is a valid tree
law dir_encode_sound:
  for +s: List<&2, Dr.Layer>
  {Tr.sound(Dr.encode(s)) == True{} : Bool}

# LAW: a resume reads back the stack the tree holds, exactly
law dir_resume_restores:
  for +s: List<&2, Dr.Layer>
  {Dr.decode(Dr.encode(s)) == s : List<&2, Dr.Layer>}

# LAW: a rewind of any valid tree to the tree of a stack restores that
# stack, exactly: a rewind removes the Directors added after the target
# and brings back the ones removed
law dir_rewind_restores:
  for +a: List<&2, Tr.Ent>
  for +s: List<&2, Dr.Layer>
  for good: {Tr.sound(a) == True{} : Bool}
  {Dr.decode(Tr.apply(a, Tr.Rewind{Tr.diff(a, Dr.encode(s))})) == s : List<&2, Dr.Layer>}

# (S6) The inference layer
# ------------------------
# docs/inference.md S6, the model in bend/infer.bend. Every input is free:
# any rulebook, query and directive; any replies of the model; any
# provider support; any tools; any stream; any context sizes.

# LAW: a rulebook with a rule of an unknown directive does not compile
law quirk_unknown_rejected:
  for +known: List<&2, Nat>
  for +pre: List<&2, If.Rule>
  for +r: If.Rule
  for +post: List<&2, If.Rule>
  for bad: {If.elem(known, If.Rule.dir(r)) == False{} : Bool}
  {If.compiles(known, List.append(&2, If.Rule, pre, r <> post)) == False{} : Bool}

# LAW: a rulebook with two rules of one layer, target and directive and
# different values does not compile: precedence is never ambiguous
law quirk_clash_rejected:
  for +known: List<&2, Nat>
  for +pre: List<&2, If.Rule>
  for +a: If.Rule
  for +mid: List<&2, If.Rule>
  for +b: If.Rule
  for +post: List<&2, If.Rule>
  for both: {If.clash(a, b) == True{} : Bool}
  {If.compiles(known, List.append(&2, If.Rule, pre, a <> List.append(&2, If.Rule, mid, b <> post))) == False{} : Bool}

# LAW: with no rule that applies, the answer is Unknown, never a guess
law quirk_unknown_when_none:
  for +rs: List<&2, If.Rule>
  for +q: If.Query
  for +d: Nat
  for none: {If.any_at(rs, q, d, 0n) == False{} : Bool}
  {If.lookup(rs, q, d) == If.Unknown{} : If.Ans}

# LAW: a rule that applies always gives an answer
law quirk_known_when_some:
  for +rs: List<&2, If.Rule>
  for +q: If.Query
  for +d: Nat
  for some: {If.any_at(rs, q, d, 0n) == True{} : Bool}
  {If.is_known(If.lookup(rs, q, d)) == True{} : Bool}

# LAW: in a rulebook that compiles, a rule of the highest layer that
# applies gives the answer: host over model over family
law quirk_highest_wins:
  for +known: List<&2, Nat>
  for +pre: List<&2, If.Rule>
  for +r: If.Rule
  for +post: List<&2, If.Rule>
  for +q: If.Query
  for ok: {If.compiles(known, List.append(&2, If.Rule, pre, r <> post)) == True{} : Bool}
  for hit: {If.applies(q, r) == True{} : Bool}
  for top: {If.any_at(List.append(&2, If.Rule, pre, r <> post), q, If.Rule.dir(r), 1n+If.Rule.rank(r)) == False{} : Bool}
  {If.lookup(List.append(&2, If.Rule, pre, r <> post), q, If.Rule.dir(r)) == If.Known{If.Rule.val(r)} : If.Ans}

# LAW: in a rulebook that compiles, the order of two rules changes no
# answer
law quirk_order_free:
  for +known: List<&2, Nat>
  for +pre: List<&2, If.Rule>
  for +a: If.Rule
  for +b: If.Rule
  for +post: List<&2, If.Rule>
  for +q: If.Query
  for +d: Nat
  for ok: {If.compiles(known, List.append(&2, If.Rule, pre, a <> b <> post)) == True{} : Bool}
  {If.lookup(List.append(&2, If.Rule, pre, b <> a <> post), q, d) == If.lookup(List.append(&2, If.Rule, pre, a <> b <> post), q, d) : If.Ans}

# LAW: the order of two rules changes nothing about whether the rulebook
# compiles
law quirk_compile_order_free:
  for +known: List<&2, Nat>
  for +pre: List<&2, If.Rule>
  for +a: If.Rule
  for +b: If.Rule
  for +post: List<&2, If.Rule>
  {If.compiles(known, List.append(&2, If.Rule, pre, b <> a <> post)) == If.compiles(known, List.append(&2, If.Rule, pre, a <> b <> post)) : Bool}

# LAW: a forced call makes at most 1 + r attempts
law force_bounded:
  for +r: Nat
  for +replies: List<&2, Bool>
  for +sup: Bool
  for +free: Bool
  {Nat.is_le(List.length(&2, If.Try, Pair.fst(List<&2, If.Try>, If.Forced, If.force(r, replies, sup, free))), 1n+r) == True{} : Bool}

# LAW: the first attempt sets the native flag only when it is supported
# and free
law force_first_flag:
  for +r: Nat
  for +replies: List<&2, Bool>
  for +sup: Bool
  for +free: Bool
  {List.head(&2, If.Try, Pair.fst(List<&2, If.Try>, If.Forced, If.force(r, replies, sup, free))) == Some{If.Try{Bool.and(sup, free)}} : Maybe<&2, If.Try>}

# LAW: every retry escalates to the native flag when it is supported
law force_retry_flag:
  for +r: Nat
  for +replies: List<&2, Bool>
  for +sup: Bool
  for +free: Bool
  {If.flags(List.drop(&2, If.Try, Pair.fst(List<&2, If.Try>, If.Forced, If.force(r, replies, sup, free)), 1n), sup) == True{} : Bool}

# LAW: a forced call reports a call exactly when the model called the
# tool within its attempts; otherwise it reports the failure
law force_reports:
  for +r: Nat
  for +replies: List<&2, Bool>
  for +sup: Bool
  for +free: Bool
  {If.Forced.called(Pair.snd(List<&2, If.Try>, If.Forced, If.force(r, replies, sup, free))) == If.called_within(1n+r, replies) : Bool}

# LAW: at most cap tools get strict schemas
law strict_within_cap:
  for +cap: Nat
  for +ts: List<&2, If.Tool>
  {Nat.is_le(List.length(&2, If.Tool, Pair.fst(List<&2, If.Tool>, List<&2, If.Tool>, If.strict(cap, ts))), cap) == True{} : Bool}

# LAW: no tool is lost: every tool is strict or loose, as many times as
# it was given
law strict_keeps_every_tool:
  for +cap: Nat
  for +ts: List<&2, If.Tool>
  for +i: Nat
  {Nat.add(If.count(Pair.fst(List<&2, If.Tool>, List<&2, If.Tool>, If.strict(cap, ts)), i), If.count(Pair.snd(List<&2, If.Tool>, List<&2, If.Tool>, If.strict(cap, ts)), i)) == If.count(ts, i) : Nat}

# LAW: every strict tool has a priority of at least every loose tool
law strict_by_priority:
  for +cap: Nat
  for +ts: List<&2, If.Tool>
  {If.dominates(Pair.fst(List<&2, If.Tool>, List<&2, If.Tool>, If.strict(cap, ts)), Pair.snd(List<&2, If.Tool>, List<&2, If.Tool>, If.strict(cap, ts))) == True{} : Bool}

# LAW: a stream that repeats a chunk k times in a row is cut
law guard_cuts_repeats:
  for +xs: List<&2, Nat>
  for +k: Nat
  for rep: {If.repeats(xs, k) == True{} : Bool}
  {If.Cut.cut(If.guard(xs, k)) == True{} : Bool}

# LAW: a stream with a window of k chunks that is periodic, with a period
# of at most k/4 (at least 1), is cut
law guard_cuts_loops:
  for +xs: List<&2, Nat>
  for +k: Nat
  for lp: {If.loops(xs, k) == True{} : Bool}
  {If.Cut.cut(If.guard(xs, k)) == True{} : Bool}

# LAW: a stream with no window of k chunks that is periodic, with a
# period of at most k/4 (at least 1), is not cut
law guard_keeps_others:
  for +xs: List<&2, Nat>
  for +k: Nat
  for calm: {If.loops(xs, k) == False{} : Bool}
  {If.guard(xs, k) == If.Whole{} : If.Cut}

# LAW: when each turn grows the context by at most m, compaction (at the
# threshold limit - m) starts at a turn before any turn over the limit
law compact_starts_early:
  for +xs: List<&2, Nat>
  for +m: Nat
  for +lim: Nat
  for small: {Nat.is_le(m, lim) == True{} : Bool}
  for steps: {If.steps_le(xs, m, 0n) == True{} : Bool}
  {If.m.lt(If.first_at(xs, Nat.sub(lim, m), 0n), If.first_at(xs, 1n+lim, 0n)) == True{} : Bool}

# (S7) The tool surface
# ---------------------
# docs/tools.md S7, the model in bend/tools.bend. Every input is free:
# any tools that join and quit, any schemas, any paths, any scripts, any
# auto set, any answers of the user.

# LAW: no event changes the roster: tools that join go behind `dyn`
law roster_fixed:
  for es: List<&2, Tl.Ev>
  for +s: Tl.Sess
  {Tl.Sess.roster(Tl.run(es, s)) == Tl.Sess.roster(s) : List<&2, Nat>}

# LAW: every request of a session sends the roster it started with
law roster_sent_fixed:
  for es: List<&2, Tl.Ev>
  for +r: List<&2, Nat>
  for d: List<&2, Nat>
  {Tl.all_eq(Tl.Sess.sent(Tl.run(es, Tl.Sess{r, d, Nil{}})), r) == True{} : Bool}

# LAW: a tool that joins is reachable through `dyn`
law dyn_reaches_joined:
  for +s: Tl.Sess
  for +t: Nat
  {Tl.dyn_call(Tl.step(s, Tl.Join{t}), t) == True{} : Bool}

# LAW: a tool that quits is not reachable through `dyn`
law dyn_drops_quit:
  for +s: Tl.Sess
  for +t: Nat
  {Tl.dyn_call(Tl.step(s, Tl.Quit{t}), t) == False{} : Bool}

# LAW: every schema the harness sends has the intent parameter
law schema_has_intent:
  for s: Tl.Schema
  {Tl.elem(Tl.Schema.params(Tl.build(s)), Tl.intent()) == True{} : Bool}

# LAW: every schema the harness sends has a version of at least 1
law schema_versioned:
  for s: Tl.Schema
  {Nat.is_le(1n, Tl.Schema.version(Tl.build(s))) == True{} : Bool}

# LAW: the harness keeps every parameter a tool declares
law schema_keeps_params:
  for +s: Tl.Schema
  for +x: Nat
  for has: {Tl.elem(Tl.Schema.params(s), x) == True{} : Bool}
  {Tl.elem(Tl.Schema.params(Tl.build(s)), x) == True{} : Bool}

# LAW: building a built schema changes nothing
law schema_build_idempotent:
  for +s: Tl.Schema
  {Tl.build(Tl.build(s)) == Tl.build(s) : Tl.Schema}

# LAW: a path that goes above its root is rejected, never clamped
law path_rejects_escape:
  for +segs: List<&2, Tl.Seg>
  for out: {Tl.stays(segs, 0n) == False{} : Bool}
  {Tl.resolve(segs) == None{} : Maybe<&2, List<&2, Nat>>}

# LAW: a path that stays under its root resolves
law path_resolves_inside:
  for +segs: List<&2, Tl.Seg>
  for inside: {Tl.stays(segs, 0n) == True{} : Bool}
  {Maybe.is_some(&2, List<&2, Nat>, Tl.resolve(segs)) == True{} : Bool}

# LAW: the steps that ran are the script's first steps, in order
law gate_prefix:
  for +ss: List<&2, Tl.Step>
  for +auto: List<&2, Nat>
  for ans: List<&2, Bool>
  {Tl.prefix(Tl.Ran.steps(Tl.exec(ss, auto, ans)), ss) == True{} : Bool}

# LAW: no more gated steps run than the user approved
law gate_needs_yes:
  for +ss: List<&2, Tl.Step>
  for +auto: List<&2, Nat>
  for +ans: List<&2, Bool>
  {Nat.is_le(Tl.gated(Tl.Ran.steps(Tl.exec(ss, auto, ans)), auto), Tl.yeses(ans)) == True{} : Bool}

# LAW: a denial stops the script at the denied step: the steps before it
# ran, it and every later step did not
law gate_deny_stops:
  for +pre: List<&2, Tl.Step>
  for +s: Tl.Step
  for +post: List<&2, Tl.Step>
  for +auto: List<&2, Nat>
  for ans: List<&2, Bool>
  for free: {Tl.gated(pre, auto) == 0n : Nat}
  for held: {Tl.auto.at(auto, s) == False{} : Bool}
  {Tl.exec(List.append(&2, Tl.Step, pre, s <> post), auto, False{} <> ans) == Tl.Ran{pre, Tl.Denied{Tl.Step.id(s)}} : Tl.Ran}

# LAW: a script that finished ran every step
law gate_finish_runs_all:
  for +ss: List<&2, Tl.Step>
  for +auto: List<&2, Nat>
  for +ans: List<&2, Bool>
  for fin: {Tl.End.finished(Tl.Ran.end(Tl.exec(ss, auto, ans))) == True{} : Bool}
  {Tl.Ran.steps(Tl.exec(ss, auto, ans)) == ss : List<&2, Tl.Step>}

# (S8) The interface
# ------------------
# docs/interface.md S8, the model in bend/screen.bend. Every input is free:
# any blocks, growths, finals, flushes and resizes in any order; any
# chunk sizes and frames; any check results; any child heights.

# LAW: committed blocks come first: the scrollback has no gap
law tx_gapless:
  for es: List<&2, Sc.Ev>
  for +w: Nat
  {Sc.gapless(Sc.Tx.blocks(Sc.run(es, Sc.Tx{Nil{}, 0n, w}))) == True{} : Bool}

# LAW: the scrollback only grows: what is committed stays, unchanged, in
# its place, whatever comes after
law tx_scrollback_append_only:
  for +pre: List<&2, Sc.Ev>
  for post: List<&2, Sc.Ev>
  for +w: Nat
  {Sc.pre(Sc.scroll(Sc.Tx.blocks(Sc.run(pre, Sc.Tx{Nil{}, 0n, w}))), Sc.scroll(Sc.Tx.blocks(Sc.run(List.append(&2, Sc.Ev, pre, post), Sc.Tx{Nil{}, 0n, w})))) == True{} : Bool}

# LAW: a resize writes no block again
law tx_resize_keeps:
  for +t: Sc.Tx
  for +w: Nat
  {Sc.Tx.blocks(Sc.step(t, Sc.Resize{w})) == Sc.Tx.blocks(t) : List<&2, Sc.Blk>}

# LAW: after a flush no final block waits: the first block not committed
# is active
law tx_flush_settles:
  for +t: Sc.Tx
  {Sc.flushed(Sc.Tx.blocks(Sc.step(t, Sc.Flush{}))) == True{} : Bool}

# LAW: the screen never shows text that did not arrive
law pace_never_ahead:
  for es: List<&2, Sc.PEv>
  for +min: Nat
  for +k: Nat
  {Nat.is_le(Sc.Pace.shown(Sc.pace.run(es, min, k, Sc.Pace{0n, 0n})), Sc.Pace.recv(Sc.pace.run(es, min, k, Sc.Pace{0n, 0n}))) == True{} : Bool}

# LAW: the screen never shows less than before
law pace_never_back:
  for +min: Nat
  for +k: Nat
  for +p: Sc.Pace
  for e: Sc.PEv
  {Nat.is_le(Sc.Pace.shown(p), Sc.Pace.shown(Sc.pace.step(min, k, p, e))) == True{} : Bool}

# LAW: with a minimum of at least 1, a backlog of b characters is all
# shown after b frames
law pace_drains:
  for +min: Nat
  for +k: Nat
  for +p: Sc.Pace
  for +n: Nat
  for one: {Nat.is_le(1n, min) == True{} : Bool}
  for behind: {Nat.is_le(Sc.Pace.shown(p), Sc.Pace.recv(p)) == True{} : Bool}
  for enough: {Nat.is_le(Nat.sub(Sc.Pace.recv(p), Sc.Pace.shown(p)), n) == True{} : Bool}
  {Sc.Pace.shown(Sc.pace.run(Sc.frames(n), min, k, p)) == Sc.Pace.recv(p) : Nat}

# LAW: only a frame that passed its check reaches the terminal, and a
# frame that failed both checks is reported
law verify_only_checked:
  for f: Nat
  for g: Nat
  for +ok1: Bool
  for +ok2: Bool
  {Sc.checked(Sc.present(f, g, ok1, ok2), ok1, ok2) == True{} : Bool}

# LAW: no child is drawn outside the viewport
law layout_inside:
  for hs: List<&2, Nat>
  for +y: Nat
  for +rows: Nat
  {Sc.inside(Sc.vstack(hs, y, rows), rows) == True{} : Bool}

# LAW: no two children overlap
law layout_apart:
  for hs: List<&2, Nat>
  for +y: Nat
  for +rows: Nat
  {Sc.apart(Sc.vstack(hs, y, rows), y) == True{} : Bool}

# LAW: children that fit are drawn whole
law layout_whole_when_room:
  for +hs: List<&2, Nat>
  for +y: Nat
  for +rows: Nat
  for fits: {Nat.is_le(Nat.add(y, Sc.sum(hs)), rows) == True{} : Bool}
  {Sc.heights(Sc.vstack(hs, y, rows)) == hs : List<&2, Nat>}

# (S9) Local tiny models
# ----------------------
# docs/inference.md S9, the model in bend/tiny.bend. Every input is free:
# any chain of models, any set of available models, any needs of any
# processes with any tags, any worker exits, in any order.

# LAW: a task uses only a model of its chain that is available
law tiny_pick_in_chain:
  for +chain: List<&2, Nat>
  for +up: List<&2, Nat>
  for +m: Nat
  for used: {Tn.pick(chain, up) == Tn.Use{m} : Tn.Pick}
  {Bool.and(Tn.elem(chain, m), Tn.elem(up, m)) == True{} : Bool}

# LAW: it uses the first available model of the chain
law tiny_pick_first:
  for +pre: List<&2, Nat>
  for +m: Nat
  for +post: List<&2, Nat>
  for +up: List<&2, Nat>
  for before: {Tn.none_up(pre, up) == True{} : Bool}
  for here: {Tn.elem(up, m) == True{} : Bool}
  {Tn.pick(List.append(&2, Nat, pre, m <> post), up) == Tn.Use{m} : Tn.Pick}

# LAW: with no model of the chain available the task fails as
# Unavailable: it never runs on a model outside the chain
law tiny_pick_unavailable:
  for +chain: List<&2, Nat>
  for +up: List<&2, Nat>
  for none: {Tn.none_up(chain, up) == True{} : Bool}
  {Tn.pick(chain, up) == Tn.Unavailable{} : Tn.Pick}

# LAW: every need of a process gets exactly one outcome: it joins, starts
# or replaces the worker
law tiny_every_need_served:
  for +es: List<&2, Tn.Ev>
  for +w: Tn.W
  {List.length(&2, Tn.Got, Tn.gots(es, w)) == Tn.needs(es) : Nat}

# LAW: after any events, the worker runs with the tag of the last need
# since the last exit: a stale worker never serves a process
law tiny_worker_current:
  for +es: List<&2, Tn.Ev>
  {Tn.W.tag(Tn.run(es, Tn.NoWorker{})) == Tn.last_tag(es, None{}) : Maybe<&2, Nat>}

# LAW: a need with the running worker's tag joins it: no restart churn
law tiny_same_tag_joins:
  for +o: Nat
  for +t: Nat
  for +p: Nat
  {Tn.got(Tn.Worker{o, t}, Tn.Need{p, t}) == [Tn.Joined{}] : List<&2, Tn.Got>}

# (S10) Reasoning depth
# ---------------------
# docs/inference.md S10, the model in bend/effort.bend. Every input is
# free: any model, reasoning or not, with any thinking-level map (each
# entry missing, null or a wire string); any level; any stored level and
# default; any model switches, sets and cycle steps, in any order.

# LAW: a model without reasoning offers off only, whatever its map
law effort_offered_plain:
  for +map: Ef.LvMap
  {Ef.offered(Ef.Mdl{False{}, map}) == [Ef.Off{}] : List<&2, Ef.Lv>}

# LAW: a reasoning model never offers a level with a null entry
law effort_offered_null:
  for +map: Ef.LvMap
  for +l: Ef.Lv
  for null: {Ef.entry(l, map) == Ef.Null{} : Ef.Ent}
  {Ef.has(Ef.offered(Ef.Mdl{True{}, map}), l) == False{} : Bool}

# LAW: a model offers xhigh or max only with a wire entry for it
law effort_offered_ext:
  for r: Bool
  for +map: Ef.LvMap
  for +l: Ef.Lv
  for x: {Ef.ext(l) == True{} : Bool}
  for in: {Ef.has(Ef.offered(Ef.Mdl{r, map}), l) == True{} : Bool}
  {Ef.entry(l, map) == Ef.Wire{} : Ef.Ent}

# LAW: a reasoning model offers every level that its map keeps (a wire
# entry, or a missing entry below xhigh)
law effort_offered_kept:
  for +map: Ef.LvMap
  for +l: Ef.Lv
  for k: {Ef.keep(map, l) == True{} : Bool}
  {Ef.has(Ef.offered(Ef.Mdl{True{}, map}), l) == True{} : Bool}

# LAW: the offered levels are strictly ascending in ladder order: no
# level comes twice
law effort_offered_asc:
  for m: Ef.Mdl
  {Ef.asc(Ef.offered(m)) == True{} : Bool}

# LAW: when the model offers a level, the clamp of any level is an
# offered level (so is the level after a model switch)
law effort_clamp_offered:
  for +m: Ef.Mdl
  for +l: Ef.Lv
  for ne: {Ef.empty(Ef.offered(m)) == False{} : Bool}
  {Ef.has(Ef.offered(m), Ef.clamp(m, l)) == True{} : Bool}

# LAW: the clamp keeps an offered level
law effort_clamp_keeps:
  for +m: Ef.Mdl
  for +l: Ef.Lv
  for in: {Ef.has(Ef.offered(m), l) == True{} : Bool}
  {Ef.clamp(m, l) == l : Ef.Lv}

# LAW: a second clamp changes nothing, also when the model offers no level
law effort_clamp_idem:
  for +m: Ef.Mdl
  for +l: Ef.Lv
  {Ef.clamp(m, Ef.clamp(m, l)) == Ef.clamp(m, l) : Ef.Lv}

# LAW: with fewer than two offered levels a cycle step changes nothing
law effort_cycle_still:
  for +m: Ef.Mdl
  for +l: Ef.Lv
  for +d: Ef.Dir
  for few: {Ef.two(Ef.offered(m)) == False{} : Bool}
  {Ef.cycle(m, l, d) == None{} : Maybe<&2, Ef.Lv>}

# LAW: forward from an offered level gives the next offered level
law effort_cycle_next:
  for +m: Ef.Mdl
  for +pre: List<&2, Ef.Lv>
  for +a: Ef.Lv
  for +b: Ef.Lv
  for +post: List<&2, Ef.Lv>
  for +split: {Ef.offered(m) == List.append(&2, Ef.Lv, pre, a <> b <> post) : List<&2, Ef.Lv>}
  {Ef.cycle(m, a, Ef.Forward{}) == Some{b} : Maybe<&2, Ef.Lv>}

# LAW: forward from the last offered level wraps to the first
law effort_cycle_wrap:
  for +m: Ef.Mdl
  for +h: Ef.Lv
  for +pre: List<&2, Ef.Lv>
  for +z: Ef.Lv
  for +split: {Ef.offered(m) == List.append(&2, Ef.Lv, h <> pre, [z]) : List<&2, Ef.Lv>}
  {Ef.cycle(m, z, Ef.Forward{}) == Some{h} : Maybe<&2, Ef.Lv>}

# LAW: backward from an offered level gives the offered level before it
law effort_cycle_prev:
  for +m: Ef.Mdl
  for +pre: List<&2, Ef.Lv>
  for +a: Ef.Lv
  for +b: Ef.Lv
  for +post: List<&2, Ef.Lv>
  for +split: {Ef.offered(m) == List.append(&2, Ef.Lv, pre, a <> b <> post) : List<&2, Ef.Lv>}
  {Ef.cycle(m, b, Ef.Backward{}) == Some{a} : Maybe<&2, Ef.Lv>}

# LAW: backward from the first offered level wraps to the last
law effort_cycle_wrap_back:
  for +m: Ef.Mdl
  for +h: Ef.Lv
  for +pre: List<&2, Ef.Lv>
  for +z: Ef.Lv
  for split: {Ef.offered(m) == List.append(&2, Ef.Lv, h <> pre, [z]) : List<&2, Ef.Lv>}
  {Ef.cycle(m, h, Ef.Backward{}) == Some{z} : Maybe<&2, Ef.Lv>}

# LAW: a backward step undoes a forward step from an offered level
law effort_cycle_inverse:
  for +m: Ef.Mdl
  for +l: Ef.Lv
  for in: {Ef.has(Ef.offered(m), l) == True{} : Bool}
  {Ef.turn(m, Ef.turn(m, l, Ef.Forward{}), Ef.Backward{}) == l : Ef.Lv}

# LAW: a forward step undoes a backward step from an offered level
law effort_cycle_inverse_back:
  for +m: Ef.Mdl
  for +l: Ef.Lv
  for in: {Ef.has(Ef.offered(m), l) == True{} : Bool}
  {Ef.turn(m, Ef.turn(m, l, Ef.Backward{}), Ef.Forward{}) == l : Ef.Lv}

# LAW: a session with no stored level shows `default`, never off
law effort_unset_default:
  for +mo: Maybe<&2, Ef.Mdl>
  {Ef.shown(Ef.Sess{mo, None{}}) == Ef.Default{} : Ef.Shown}

# LAW: open settles the stored level on an offered level when the model
# offers one
law effort_settle_offered:
  for +m: Ef.Mdl
  for +st: Maybe<&2, Ef.Lv>
  for +dflt: Ef.Lv
  for +k: Ef.Lv
  for ne: {Ef.empty(Ef.offered(m)) == False{} : Bool}
  for settled: {Ef.Sess.stored(Ef.open(Ef.Sess{Some{m}, st}, dflt)) == Some{k} : Maybe<&2, Ef.Lv>}
  {Ef.has(Ef.offered(m), k) == True{} : Bool}

# LAW: after open and any actions, the session stores the level it sends
law effort_stored_is_sent:
  for +s: Ef.Sess
  for +dflt: Ef.Lv
  for +acts: List<&2, Ef.Act>
  {Ef.Sess.stored(Ef.run(acts, Ef.open(s, dflt))) == Some{Ef.sent(Ef.run(acts, Ef.open(s, dflt)))} : Maybe<&2, Ef.Lv>}

# LAW: after open and any actions, the display shows the level the
# session sends
law effort_shown_is_sent:
  for +s: Ef.Sess
  for +dflt: Ef.Lv
  for +acts: List<&2, Ef.Act>
  {Ef.shown(Ef.run(acts, Ef.open(s, dflt))) == Ef.Level{Ef.sent(Ef.run(acts, Ef.open(s, dflt)))} : Ef.Shown}

# (H4) Every run ends
# -------------------
# docs/harness.md H4, the model in bend/run.bend: one run (one user turn)
# through prepare, call (a request or a deferred poll), compact (an
# overflow's or a blocking threshold one) and tools. Every input is free:
# any model reply, any round end, any compaction result, an abort, in any
# order.

# LAW: every run has ended (answered, aborted or failed) after bound(cfg)
# inputs, whatever they are and whatever follows them; bound(cfg) =
# max(cap, 1)·(2 + (retries + notes + 2)·(polls + 2)), from
# maxToolRounds, MAX_POLLS, retry.maxRetries, MAX_NOTES and one
# compaction a generation. Notes have their own budget: a noted retry
# spends a note, never a retry
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
  Or({Rn.failed(Rn.run(cfg, evs)) == True{} : Bool}, {Nat.is_lt(Rn.rounds(cfg, evs), Nat.max(Rn.Cfg.cap(cfg), 1n)) == True{} : Bool})

# The loop guard of H4.3 (run_loop_needs_repeats) is gone. The law
# `rec_never_runs_a_repeat` (H4.8) replaces it, and it is stronger: no
# row of the same calls with the same results ever gets to REPEAT_CALLS
# (5) rounds. The loop guard failed a run only after 6 such rounds.

# LAW: the round cap fails a run only at its max(cap, 1)th round, never
# earlier
law run_rounds_fail_at_cap:
  for +cfg: Rn.Cfg
  for +evs: List<&2, Rn.Ev>
  Or({Rn.capped(Rn.run(cfg, evs)) == False{} : Bool}, {Rn.rounds(cfg, evs) == Nat.max(Rn.Cfg.cap(cfg), 1n) : Nat})

# LAW: the poll cap fails a run only when its request's reply and each of
# its `polls` polls were deferred, polls + 1 deferred replies in a row
law run_polls_need_defers:
  for +cfg: Rn.Cfg
  for +evs: List<&2, Rn.Ev>
  Or({Rn.polled(Rn.run(cfg, evs)) == False{} : Bool}, {Rn.defers(cfg, evs) == 1n+Rn.Cfg.polls(cfg) : Nat})

# LAW: a message that ends the model's turn (any stop reason) with no
# text and no tool call never answers the run (H4.7): the model gave no
# answer, so the step is a noted error's: a retry with a note while
# notes are left, else the run fails on the model
law run_no_answer_is_an_error:
  for +cfg: Rn.Cfg
  for +r: Nat
  for +c: Nat
  for +a: Nat
  for +n: Nat
  for +p: Nat
  {Rn.call(cfg, Rn.Ended.reply(Rn.Ended{False{}, False{}}), r, c, a, n, p) == Rn.note(cfg, r, c, a, n, p) : Rn.St}

# LAW: a message that ends the model's turn with a tool call never
# answers the run: its calls go to the tools phase, whatever its text and
# its stop reason. vLLM, llama.cpp and Ollama send the stop reason stop
# with tool calls
law run_calls_never_answer:
  for +cfg: Rn.Cfg
  for text: Bool
  for +r: Nat
  for +c: Nat
  for +a: Nat
  for +n: Nat
  for +p: Nat
  {Rn.call(cfg, Rn.Ended.reply(Rn.Ended{text, True{}}), r, c, a, n, p) == Rn.St{Rn.Tools{}, r, c, a, n, p} : Rn.St}

# LAW: a noted error spends a note, not a retry: retryable or not, it is
# retried with a note while notes are left, and the retries left stay
law run_note_spends_no_retry:
  for +cfg: Rn.Cfg
  for retryable: Bool
  for +r: Nat
  for +c: Nat
  for +a: Nat
  for +m: Nat
  for +p: Nat
  {Rn.call(cfg, Rn.Error{retryable, True{}}, r, c, a, 1n+m, p) == Rn.St{Rn.Prepare{}, r, c, a, m, Rn.Cfg.polls(cfg)} : Rn.St}

# LAW: a retryable error that is not noted spends a retry, not a note:
# the notes left stay
law run_retry_spends_no_note:
  for +cfg: Rn.Cfg
  for +r: Nat
  for +c: Nat
  for +b: Nat
  for +n: Nat
  for +p: Nat
  {Rn.call(cfg, Rn.Error{True{}, False{}}, r, c, 1n+b, n, p) == Rn.St{Rn.Prepare{}, r, c, b, n, Rn.Cfg.polls(cfg)} : Rn.St}

# (H4.7) A retry never resends a request it cut
# ---------------------------------------------
# docs/harness.md H4.7, the requests of bend/run.bend: a model decodes
# the same request the same way (a greedy one always does), so a retry
# after a noted reply (the stream repeated itself until the guard cut it,
# or the reply gave no answer) ends its request with a harness note that
# names the retry's attempt. A request is the version of its logged
# context and the attempt its note names.

# LAW: no request the run sends is equal to a request it sent before and
# had cut: a retry after a cut sends neither the request it cut nor any
# other one the run cut, whatever the inputs, cut after cut until the
# notes run out
law run_retry_sends_a_new_request:
  for +cfg: Rn.Cfg
  for +evs: List<&2, Rn.Ev>
  {Rn.fresh(Rn.Reqs.log(Rn.reqs(cfg, evs))) == True{} : Bool}

# LAW: a noted reply cuts the request the run sent, and the next request
# carries the note of the next attempt
law run_cut_names_the_request:
  for -retryable: Bool
  for -fin: Rn.Fin
  for -got: Rn.Got
  for -pa: Rn.Ph
  for -ctx: Nat
  for -n: Nat
  for -note: Nat
  for -log: List<&2, Rn.Sent>
  {Rn.Reqs.step(Rn.Call{}, Rn.Go{Rn.Error{retryable, True{}}, fin, got}, pa, Rn.Reqs{ctx, n, note, log}) == Rn.Reqs{ctx, 1n+n, 1n+n, Rn.Cut{Rn.Req{ctx, note}} <> log} : Rn.Reqs}

# LAW: the note changes what the model reads, never what the run logs:
# a request logs the same lines as its context with no note
law run_note_is_never_logged:
  for q: Rn.Req
  {Rn.logged(Rn.Req.lines(q)) == Rn.logged(Rn.Req.lines(Rn.Req{Rn.Req.ctx(q), 0n})) : List<&2, Rn.Line>}
