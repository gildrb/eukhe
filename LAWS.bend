# LAWS: every law of eukhe, one section per area. The first section is
# what eukhe's chat memory must do, after Victor Taelin's OptChat gist:
# each law is an open claim about the model in bend/optchat.bend.
# docs/memory.md maps each gist rule to the Rust code and to the law (or
# test) that secures it. Each later section starts with `# ---- <area> ----`
# and its requirement table. The models live in bend/<area>.bend;
# PROOF.bend proves every law, as Laws.<law>.
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
import ./bend/semver.bend as Sv
import ./bend/auth_flight.bend as F
import ./bend/theme.bend as T
import ./bend/color.bend as Co
import ./bend/tokens.bend as Tk
import ./bend/progress.bend as Pr
import ./bend/aux_fallback.bend as Af
import ./bend/skill_load.bend as Sk
import ./bend/kernel_local.bend as KL
import ./bend/log.bend as Lg
import ./bend/staging.bend as Sg
import ./bend/catalog_union.bend as CU
import ./bend/cron.bend as Cr
import ./bend/supervise.bend as Su
import ./bend/revive.bend as Rv
import ./bend/orphan.bend as Or
import ./bend/launcher.bend as La
import ./bend/replace.bend as Rp
import ./bend/notice.bend as No
import ./bend/gateway_width.bend as Gw
import ./bend/tui_color.bend as TC
import ./bend/fsmode.bend as Fs
import ./bend/path_policy.bend as Pp
import ./bend/child_env.bend as Env
import ./bend/runners.bend as Ru
import ./bend/approvals.bend as Am
import ./bend/retry.bend as R
import ./bend/facts.bend as Fx
import ./bend/dash.bend as Da
import ./bend/doc_seen.bend as Ds
import ./bend/doc_commit.bend as Cm
import ./bend/doc_search.bend as Sr
import ./bend/doc_lines.bend as Dl
import ./bend/doc_tags.bend as Dt
import ./bend/config.bend as Cf
import ./bend/default_model.bend as Dm
import ./bend/workflow.bend as W
import ./bend/ffi_admission.bend as FAd
import ./bend/ffi_workflow.bend as FW
import ./bend/ffi_default_model.bend as FDm
import ./bend/ffi_aux_fallback.bend as FAf
import ./bend/wire.bend as Wr
import ./bend/ffi_doc_seen.bend as Fds
import ./bend/ffi_doc_lines.bend as Fdl
import ./bend/ffi_child.bend as FCh
import ./bend/ffi_job.bend as FJb
import ./bend/ffi_progress.bend as FPr
import ./bend/ffi_sandbox.bend as FSb

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

# The task's decisions, as the Rust task runs them (bend/child.bend
# `verdict`, `owe.next`, `cut.ph`): the call on one poll, the report
# phase's move, the abort.

# the call a task in mode m makes on the watch's verdict x: watch on,
# report to the parent's inbox, or (a silent task, or a child that
# replied) end with no report, keeping why
def ChildActed(x: Ch.Next, m: Ch.Mode) -> Ch.Call:
  match x:
    case Ch.Watch{w}:
      Ch.Watches{w}
    case Ch.Owe{k}:
      match m:
        case Ch.Inbox{}:
          Ch.Reports{k}
        case Ch.Silent{}:
          Ch.Settles{Some{k}}
    case Ch.Quiet{}:
      Ch.Settles{None{}}

# the report phase's move on the fate of submission n: none yet, submit
# it under n; queued, wait; withdrawn, owe it under n + 1; placed, end
def ChildMove(f: Maybe<&2, Ch.Fate>, +n: Nat) -> Ch.Move:
  match f:
    case None{}:
      Ch.Submit{n}
    case Some{x}:
      match x:
        case Ch.Queued{}:
          Ch.Await{}
        case Ch.Withdrawn{}:
          Ch.Resubmit{1n+n}
        case Ch.Placed{}:
          Ch.Delivered{}

# the phase an abort leaves: a delete of a watched child owes a cancelled
# report under the first id, a cancel owes nothing, an owed report goes
# on as it was, an ended task stays ended
def ChildAbort(ph: Ch.Ph, del: Bool) -> Ch.Ph:
  match ph:
    case Ch.Watching{w}:
      match del:
        case True{}:
          Ch.Owing{Ch.Cancelled{}, 1n}
        case False{}:
          Ch.Ended{}
    case Ch.Owing{k, n}:
      Ch.Owing{k, n}
    case Ch.Ended{}:
      Ch.Ended{}

# LAW: the task's call on a poll is the watch's verdict (`look`, which
# the laws above bound) as the task's mode acts on it
# EXCLUDES: a call that drops or invents a report, a silent task that
# reports, an inbox task that settles a child that owes a report
law child_task_call:
  for +cfg: Ch.Cfg
  for +w: Ch.W
  for +e: Nat
  for o: Ch.Obs
  for m: Ch.Mode
  {Ch.verdict(cfg, w, e, o, m) == ChildActed(Ch.look(cfg, w, e, o), m) : Ch.Call}

# LAW: a silent task never reports to its parent
law child_silent_never_reports:
  for +cfg: Ch.Cfg
  for +w: Ch.W
  for +e: Nat
  for o: Ch.Obs
  {Ch.Call.reports(Ch.verdict(cfg, w, e, o, Ch.Silent{})) == False{} : Bool}

# LAW: the report phase's move is the one report rule
# EXCLUDES: a second submission while one is queued, a resubmission under
# the same id, an end before the report is placed
law child_report_move:
  for f: Maybe<&2, Ch.Fate>
  for +n: Nat
  {Ch.owe.next(f, n) == ChildMove(f, n) : Ch.Move}

# LAW: the move, carried out, is the model's report rule `owe`, so the
# report laws above hold for the task the Rust code runs
law child_report_move_is_owe:
  for f: Maybe<&2, Ch.Fate>
  for k: Ch.Report
  for +n: Nat
  for open: Bool
  for inbox: List<&2, Ch.Sub>
  {Ch.owe.do(Ch.owe.next(f, n), k, n, open, inbox) == Ch.owe(f, k, n, open, inbox) : Ch.St}

# LAW: the abort's rule
# EXCLUDES: a delete with no report, a cancel that reports, an abort that
# loses or restarts an owed report
law child_abort_rule:
  for ph: Ch.Ph
  for del: Bool
  {Ch.cut.ph(ph, del) == ChildAbort(ph, del) : Ch.Ph}

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

# The live controller (Ad.Live, what eukhe runs) keeps only the live
# tickets, each with its ticket number: an ended ticket leaves, so an op
# costs the live tickets, not every ticket the provider ever admitted.
# Spec helpers: the live tickets of the model's state, numbered.

# ticket k of class c and status s before rest, when it is live
def adl_keep(s: Ad.Sts, k: Nat, c: Ad.Cls, rest: List<&2, Ad.Lv>) -> List<&2, Ad.Lv>:
  match s:
    case Ad.Queued{}:
      Ad.Lv{k, c, Ad.Queued{}} <> rest
    case Ad.Granted{}:
      Ad.Lv{k, c, Ad.Granted{}} <> rest
    case Ad.Held{}:
      Ad.Lv{k, c, Ad.Held{}} <> rest
    case Ad.Preempted{}:
      Ad.Lv{k, c, Ad.Preempted{}} <> rest
    case Ad.Ended{}:
      rest

# the live tickets of ts, the first numbered k
def adl_lives(ts: List<&2, Ad.Tk>, +k: Nat) -> List<&2, Ad.Lv>:
  match ts:
    case Nil{}:
      Nil{}
    case Ad.Tk{c, s} <> r:
      adl_keep(s, k, c, adl_lives(r, 1n+k))

# the model's state as the live controller holds it: the limits, the
# live tickets with their numbers, and the number of the next ticket
def adl_live(s: Ad.St) -> Ad.Live:
  match s:
    case Ad.St{l, q, +ts}:
      Ad.Live{l, q, adl_lives(ts, 0n), List.length(&2, Ad.Tk, ts)}

# LAW: on any state of the model, an op of the live controller does what
# the model's op does, the ended tickets left out
# EXCLUDES: every difference between the live controller and the model
#   (a grant, a preemption, a rejection, a lost or renumbered ticket, an
#   ended ticket kept or revived); with admission_live_run it carries
#   every admission law above to the controller eukhe runs
law admission_live_step:
  for +s: Ad.St
  for +o: Ad.Op
  {Ad.Live.step(adl_live(s), o) == adl_live(Ad.step(s, o)) : Ad.Live}

# LAW: after any history, the live controller holds the model's live
# tickets, numbered as the model numbers them
# EXCLUDES: a controller that drifts from the model over a history
law admission_live_run:
  for l: Ad.Lim
  for q: Nat
  for os: List<&2, Ad.Op>
  {Ad.Live.run(os, Ad.Live.new(l, q)) == adl_live(Ad.run(os, Ad.St.new(l, q))) : Ad.Live}

# LAW anchor: at a limit of one, a released permit leaves and its slot
# goes to the waiter, which keeps its number
# EXCLUDES: an ended ticket kept, tickets renumbered when one leaves
law admission_live_example:
  {Ad.Live.run([Ad.Admit{Ad.Ia{}}, Ad.Admit{Ad.Ia{}}, Ad.Release{0n}], Ad.Live.new(Ad.Cap{0n}, 1n)) == Ad.Live{Ad.Cap{0n}, 1n, [Ad.Lv{1n, Ad.Ia{}, Ad.Granted{}}], 2n} : Ad.Live}

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

# The step the Rust jobs run is `feed` (bend/job.bend): `step` with a
# job's bytes kept plus dropped held to t (t = 10^14 - 1 in the compiled
# core: the largest Nat its wire carries). Every law below holds for every t.

# an event that writes output
def JobWrites(e: Jb.JEv) -> Bool:
  match e:
    case Jb.Out{n}:
      True{}
    case Jb.Quit{c}:
      False{}
    case Jb.Kill{}:
      False{}
    case Jb.Tick{}:
      False{}

# LAW: output that fits below t is the step: nothing is cut
law job_feed_fits:
  for +t: Nat
  for +cap: Maybe<&2, Nat>
  for +k: Nat
  for +d: Nat
  for +n: Nat
  for fits: {Nat.is_le(Nat.add(Nat.add(k, d), n), t) == True{} : Bool}
  {Jb.feed(t, cap, Jb.Live{k, d}, Jb.Out{n}) == Jb.step(cap, Jb.Live{k, d}, Jb.Out{n}) : Jb.J}

# LAW: an event that writes no output is the step
law job_feed_no_output:
  for +t: Nat
  for +cap: Maybe<&2, Nat>
  for j: Jb.J
  for e: Jb.JEv
  for quiet: {JobWrites(e) == False{} : Bool}
  {Jb.feed(t, cap, j, e) == Jb.step(cap, j, e) : Jb.J}

# LAW: an ended job stays as it ended
law job_feed_ended:
  for +t: Nat
  for +cap: Maybe<&2, Nat>
  for +k: Nat
  for +d: Nat
  for +x: Jb.End
  for e: Jb.JEv
  {Jb.feed(t, cap, Jb.Ended{k, d, x}, e) == Jb.Ended{k, d, x} : Jb.J}

# LAW: any output is a step on a part of it, so the cap laws above hold
# for what the Rust jobs count
law job_feed_is_a_step:
  for +t: Nat
  for +cap: Maybe<&2, Nat>
  for +k: Nat
  for +d: Nat
  for +n: Nat
  exs m: Nat
  {Jb.feed(t, cap, Jb.Live{k, d}, Jb.Out{n}) == Jb.step(cap, Jb.Live{k, d}, Jb.Out{m}) : Jb.J}

# LAW: the bytes kept plus dropped never pass t
# EXCLUDES: a count past the compiled core's Nat range (the process stops)
law job_feed_bounded:
  for +t: Nat
  for +cap: Maybe<&2, Nat>
  for +j: Jb.J
  for e: Jb.JEv
  for below: {Nat.is_le(Jb.J.total(j), t) == True{} : Bool}
  {Nat.is_le(Jb.J.total(Jb.feed(t, cap, j, e)), t) == True{} : Bool}

# LAW: output past t fills the counts to exactly t: they saturate
# EXCLUDES: output past t that is dropped whole or counted short
law job_feed_fills:
  for +t: Nat
  for +cap: Maybe<&2, Nat>
  for +k: Nat
  for +d: Nat
  for +n: Nat
  for below: {Nat.is_le(Nat.add(k, d), t) == True{} : Bool}
  for over: {Nat.is_lt(t, Nat.add(Nat.add(k, d), n)) == True{} : Bool}
  {Jb.J.total(Jb.feed(t, cap, Jb.Live{k, d}, Jb.Out{n})) == t : Nat}

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

# The plan of one path the Rust hand-back runs (bend/sandbox.bend
# `plan`): the parent's content stays (taken: both made the same change),
# a conflict, the child's file goes in, or the child's removal does.

def CowPlan.go(calm: Bool, still: Bool, same: Bool, c: Maybe<&2, Nat>) -> Sb.Plan:
  match calm:
    case True{}:
      Sb.Keep{False{}}
    case False{}:
      match still:
        case True{}:
          match c:
            case None{}:
              Sb.Drop{}
            case Some{x}:
              Sb.Take{}
        case False{}:
          match same:
            case True{}:
              Sb.Keep{True{}}
            case False{}:
              Sb.Clash{}

# the child did not change the path: keep; only the child changed it:
# its file (or its removal) goes in; both changed it alike: keep, taken;
# both changed it differently: a conflict
def CowPlan(+p: Maybe<&2, Nat>, +b: Maybe<&2, Nat>, +c: Maybe<&2, Nat>) -> Sb.Plan:
  CowPlan.go(Sb.m.eq(c, b), Sb.m.eq(p, b), Sb.m.eq(p, c), c)

# LAW: the plan of a path is the copy-on-write rule
# EXCLUDES: a lost change of either side, a conflict reported as taken, a
# removal written as a file
law cow_plan:
  for +p: Maybe<&2, Nat>
  for +b: Maybe<&2, Nat>
  for +c: Maybe<&2, Nat>
  {Sb.plan(p, b, c) == CowPlan(p, b, c) : Sb.Plan}

# LAW: the plan carries out the merge of the path, so the hand-back laws
# above hold for the Rust hand-back
law cow_plan_is_merge:
  for +p: Maybe<&2, Nat>
  for +b: Maybe<&2, Nat>
  for +c: Maybe<&2, Nat>
  {Sb.Plan.merge(Sb.plan(p, b, c), p, c) == Sb.merge1(p, b, c) : Sb.One}

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

# LAW: an alias that runs itself is a cycle, not an endless expansion;
# the cycle names the alias
law alias_self_cycle:
  for +n: Nat
  for +as: List<&2, Cv.Alias>
  {Cv.expand([Cv.CRun{n}], Cv.Alias{n, [Cv.CRun{n}]} <> as) == Cv.Cycle{n} : Cv.Exp}

# LAW: a run of an alias that does not exist is reported, with its name
law alias_unknown_reported:
  for +n: Nat
  for +as: List<&2, Cv.Alias>
  for gone: {Cv.body(as, n) == [Cv.CGone{n}] : List<&2, Cv.Cmd>}
  {Cv.expand([Cv.CRun{n}], as) == Cv.Unknown{n} : Cv.Exp}

# LAW: an alias with plain commands runs exactly its commands
law alias_runs_body:
  for +n: Nat
  for +b: List<&2, Cv.Cmd>
  for +as: List<&2, Cv.Alias>
  for flat: {Cv.plain(b) == True{} : Bool}
  {Cv.expand([Cv.CRun{n}], Cv.Alias{n, b} <> as) == Cv.Flat{b} : Cv.Exp}

# two expansions one after the other: the commands of both, in order, or
# the first error (an error of the first stops it before the second)
def cvar_cat(a: Cv.Exp, b: Cv.Exp) -> Cv.Exp:
  match a:
    case Cv.Flat{x}:
      match b:
        case Cv.Flat{y}:
          Cv.Flat{List.append(&2, Cv.Cmd, x, y)}
        case Cv.Cycle{n}:
          Cv.Cycle{n}
        case Cv.Unknown{n}:
          Cv.Unknown{n}
    case Cv.Cycle{n}:
      Cv.Cycle{n}
    case Cv.Unknown{n}:
      Cv.Unknown{n}

# LAW: a list expands command by command, in order: the expansion of two
# lists one after the other is the first's commands then the second's,
# and the first error, left to right, is the outcome
law alias_expands_in_order:
  for +cs: List<&2, Cv.Cmd>
  for +more: List<&2, Cv.Cmd>
  for +as: List<&2, Cv.Alias>
  {Cv.expand(List.append(&2, Cv.Cmd, cs, more), as) == cvar_cat(Cv.expand(cs, as), Cv.expand(more, as)) : Cv.Exp}

# LAW: anchor (the Rust test of expand): aliases a = [set x, run b],
# b = [set y], loop = [run loop2], loop2 = [run loop], gone = [run
# missing] (numbered 0 to 4, missing 5, the cvars x y z q 10 to 13):
# [run a, set z] runs x, y, z; [run loop] is a cycle at loop; [run gone]
# names missing; [set q, run loop, run missing] stops at the cycle
law alias_expand_example:
  {[Cv.expand([Cv.CRun{0n}, Cv.CToggle{12n}], [Cv.Alias{0n, [Cv.CToggle{10n}, Cv.CRun{1n}]}, Cv.Alias{1n, [Cv.CToggle{11n}]}, Cv.Alias{2n, [Cv.CRun{3n}]}, Cv.Alias{3n, [Cv.CRun{2n}]}, Cv.Alias{4n, [Cv.CRun{5n}]}]), Cv.expand([Cv.CRun{2n}], [Cv.Alias{0n, [Cv.CToggle{10n}, Cv.CRun{1n}]}, Cv.Alias{1n, [Cv.CToggle{11n}]}, Cv.Alias{2n, [Cv.CRun{3n}]}, Cv.Alias{3n, [Cv.CRun{2n}]}, Cv.Alias{4n, [Cv.CRun{5n}]}]), Cv.expand([Cv.CRun{4n}], [Cv.Alias{0n, [Cv.CToggle{10n}, Cv.CRun{1n}]}, Cv.Alias{1n, [Cv.CToggle{11n}]}, Cv.Alias{2n, [Cv.CRun{3n}]}, Cv.Alias{3n, [Cv.CRun{2n}]}, Cv.Alias{4n, [Cv.CRun{5n}]}]), Cv.expand([Cv.CToggle{13n}, Cv.CRun{2n}, Cv.CRun{5n}], [Cv.Alias{0n, [Cv.CToggle{10n}, Cv.CRun{1n}]}, Cv.Alias{1n, [Cv.CToggle{11n}]}, Cv.Alias{2n, [Cv.CRun{3n}]}, Cv.Alias{3n, [Cv.CRun{2n}]}, Cv.Alias{4n, [Cv.CRun{5n}]}])] == [Cv.Flat{[Cv.CToggle{10n}, Cv.CToggle{11n}, Cv.CToggle{12n}]}, Cv.Cycle{2n}, Cv.Unknown{5n}, Cv.Cycle{2n}] : List<&2, Cv.Exp>}

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

# The rule, verdict by verdict (bend/director.bend `decide.go`): one
# decision of the stack (top first) on the verdicts (top first), with room
# telling whether the whole stack holds fewer than cap layers and stay
# telling whether the loop ends (a layer that leads stays) or goes on (it
# leaves). Together these laws give every decision exactly.

# the decision d with the layer l put back on top of its stack
def dir_on_top(+l: Dr.Layer, d: Dr.Dec) -> Dr.Dec:
  match d:
    case Dr.Dec{o, s}:
      Dr.Dec{o, l <> s}

# LAW: with no layer left, the loop hands back with an empty stack
law dir_go_empty:
  for vs: List<&2, Dr.Verdict>
  for +room: Bool
  for +stay: Bool
  {Dr.decide.go(Nil{}, vs, room, stay) == Dr.Dec{Dr.Hand{}, Nil{}} : Dr.Dec}

# LAW: a layer with no verdict defers: it stays on top of the decision of
# the layers below, which have no verdict either
law dir_go_unjudged:
  for +l: Dr.Layer
  for +rest: List<&2, Dr.Layer>
  for +room: Bool
  for +stay: Bool
  {Dr.decide.go(l <> rest, Nil{}, room, stay) == dir_on_top(l, Dr.decide.go(rest, Nil{}, room, stay)) : Dr.Dec}

# LAW: a Defer stays on top of the decision of the layers below
law dir_go_defer:
  for +l: Dr.Layer
  for +rest: List<&2, Dr.Layer>
  for vs: List<&2, Dr.Verdict>
  for +room: Bool
  for +stay: Bool
  {Dr.decide.go(l <> rest, Dr.Defer{} <> vs, room, stay) == dir_on_top(l, Dr.decide.go(rest, vs, room, stay)) : Dr.Dec}

# LAW: a Leave removes the layer; the layers below decide
law dir_go_leave:
  for +l: Dr.Layer
  for +rest: List<&2, Dr.Layer>
  for vs: List<&2, Dr.Verdict>
  for +room: Bool
  for +stay: Bool
  {Dr.decide.go(l <> rest, Dr.Leave{} <> vs, room, stay) == Dr.decide.go(rest, vs, room, stay) : Dr.Dec}

# LAW: a Lead stays when the loop ends: it stays on top of the decision of
# the layers below
law dir_go_lead_stays:
  for +l: Dr.Layer
  for +rest: List<&2, Dr.Layer>
  for vs: List<&2, Dr.Verdict>
  for +room: Bool
  {Dr.decide.go(l <> rest, Dr.Lead{} <> vs, room, True{}) == dir_on_top(l, Dr.decide.go(rest, vs, room, True{})) : Dr.Dec}

# LAW: a Lead leaves when the loop goes on; the layers below decide
law dir_go_lead_leaves:
  for +l: Dr.Layer
  for +rest: List<&2, Dr.Layer>
  for vs: List<&2, Dr.Verdict>
  for +room: Bool
  {Dr.decide.go(l <> rest, Dr.Lead{} <> vs, room, False{}) == Dr.decide.go(rest, vs, room, False{}) : Dr.Dec}

# LAW: a Yield hands back; the stack stays as it is
law dir_go_yield:
  for +l: Dr.Layer
  for +rest: List<&2, Dr.Layer>
  for vs: List<&2, Dr.Verdict>
  for +room: Bool
  for +stay: Bool
  {Dr.decide.go(l <> rest, Dr.Yield{} <> vs, room, stay) == Dr.Dec{Dr.Hand{}, l <> rest} : Dr.Dec}

# LAW: an Abort fails; the stack stays as it is
law dir_go_abort:
  for +l: Dr.Layer
  for +rest: List<&2, Dr.Layer>
  for vs: List<&2, Dr.Verdict>
  for +room: Bool
  for +stay: Bool
  {Dr.decide.go(l <> rest, Dr.Abort{} <> vs, room, stay) == Dr.Dec{Dr.Failed{}, l <> rest} : Dr.Dec}

# LAW: an Again with budget goes on and costs the layer one unit
law dir_go_again:
  for +k: Nat
  for +b: Nat
  for +rest: List<&2, Dr.Layer>
  for vs: List<&2, Dr.Verdict>
  for +room: Bool
  for +stay: Bool
  {Dr.decide.go(Dr.Layer{k, 1n+b} <> rest, Dr.Again{} <> vs, room, stay) == Dr.Dec{Dr.Cont{}, Dr.Layer{k, b} <> rest} : Dr.Dec}

# LAW: an Again with no budget left hands back; the stack stays
law dir_go_again_spent:
  for +k: Nat
  for +rest: List<&2, Dr.Layer>
  for vs: List<&2, Dr.Verdict>
  for +room: Bool
  for +stay: Bool
  {Dr.decide.go(Dr.Layer{k, 0n} <> rest, Dr.Again{} <> vs, room, stay) == Dr.Dec{Dr.Hand{}, Dr.Layer{k, 0n} <> rest} : Dr.Dec}

# LAW: a Stack with budget and room puts the new layer on top, goes on,
# and costs the layer one unit
law dir_go_push:
  for +k: Nat
  for +b: Nat
  for +n: Dr.Layer
  for +rest: List<&2, Dr.Layer>
  for vs: List<&2, Dr.Verdict>
  for +stay: Bool
  {Dr.decide.go(Dr.Layer{k, 1n+b} <> rest, Dr.Stack{n} <> vs, True{}, stay) == Dr.Dec{Dr.Cont{}, n <> Dr.Layer{k, b} <> rest} : Dr.Dec}

# LAW: a Stack with budget and no room fails; it still costs the layer
# one unit, and the layers above the deciding one are gone
law dir_go_push_full:
  for +k: Nat
  for +b: Nat
  for +n: Dr.Layer
  for +rest: List<&2, Dr.Layer>
  for vs: List<&2, Dr.Verdict>
  for +stay: Bool
  {Dr.decide.go(Dr.Layer{k, 1n+b} <> rest, Dr.Stack{n} <> vs, False{}, stay) == Dr.Dec{Dr.Failed{}, Dr.Layer{k, b} <> rest} : Dr.Dec}

# LAW: a Stack with no budget left hands back; nothing is pushed
law dir_go_push_spent:
  for +k: Nat
  for +n: Dr.Layer
  for +rest: List<&2, Dr.Layer>
  for vs: List<&2, Dr.Verdict>
  for +room: Bool
  for +stay: Bool
  {Dr.decide.go(Dr.Layer{k, 0n} <> rest, Dr.Stack{n} <> vs, room, stay) == Dr.Dec{Dr.Hand{}, Dr.Layer{k, 0n} <> rest} : Dr.Dec}

# LAW: the room of a decision: the whole stack (every layer, those above
# the deciding one too) holds fewer than cap layers. A cap at 2^48-1 (the
# saturated setting) leaves room for every stack the cap allows.
law dir_room:
  for +s: List<&2, Dr.Layer>
  for vs: List<&2, Dr.Verdict>
  for +cap: Nat
  for +stay: Bool
  {Dr.decide.as(s, vs, cap, stay) == Dr.decide.go(s, vs, Nat.is_lt(List.length(&2, Dr.Layer, s), cap), stay) : Dr.Dec}

# LAW: a decision of the loop is the one where a layer that leads leaves
law dir_decide_goes_on:
  for +s: List<&2, Dr.Layer>
  for vs: List<&2, Dr.Verdict>
  for +cap: Nat
  {Dr.decide(s, vs, cap) == Dr.decide.as(s, vs, cap, False{}) : Dr.Dec}

# The loop, step by step (with dir_end_is_final, every tick exactly)

# LAW: a continue with a step left goes on, one step fewer, with the
# decision's stack (a layer that leads left with it)
law dir_tick_goes_on:
  for +cap: Nat
  for +n: Nat
  for +s: List<&2, Dr.Layer>
  for +vs: List<&2, Dr.Verdict>
  for +t: List<&2, Dr.Layer>
  for go: {Dr.decide(s, vs, cap) == Dr.Dec{Dr.Cont{}, t} : Dr.Dec}
  {Dr.tick(cap, Dr.Loop{1n+n, s, None{}}, vs) == Dr.Loop{n, t, None{}} : Dr.Loop}

# LAW: a continue with no step left yields; a layer that leads stays
law dir_tick_out_of_steps:
  for +cap: Nat
  for +s: List<&2, Dr.Layer>
  for +vs: List<&2, Dr.Verdict>
  for go: {Dr.Dec.out(Dr.decide(s, vs, cap)) == Dr.Cont{} : Dr.Out}
  {Dr.tick(cap, Dr.Loop{0n, s, None{}}, vs) == Dr.Loop{0n, Dr.Dec.stack(Dr.decide.as(s, vs, cap, True{})), Some{Dr.Hand{}}} : Dr.Loop}

# LAW: a hand back ends the loop with its steps left; a layer that leads
# stays
law dir_tick_hands_back:
  for +cap: Nat
  for +n: Nat
  for +s: List<&2, Dr.Layer>
  for +vs: List<&2, Dr.Verdict>
  for h: {Dr.Dec.out(Dr.decide(s, vs, cap)) == Dr.Hand{} : Dr.Out}
  {Dr.tick(cap, Dr.Loop{n, s, None{}}, vs) == Dr.Loop{n, Dr.Dec.stack(Dr.decide.as(s, vs, cap, True{})), Some{Dr.Hand{}}} : Dr.Loop}

# LAW: a failure ends the loop with its steps left; a layer that leads
# stays
law dir_tick_fails:
  for +cap: Nat
  for +n: Nat
  for +s: List<&2, Dr.Layer>
  for +vs: List<&2, Dr.Verdict>
  for f: {Dr.Dec.out(Dr.decide(s, vs, cap)) == Dr.Failed{} : Dr.Out}
  {Dr.tick(cap, Dr.Loop{n, s, None{}}, vs) == Dr.Loop{n, Dr.Dec.stack(Dr.decide.as(s, vs, cap, True{})), Some{Dr.Failed{}}} : Dr.Loop}

# A reminder leaves only with the continuation it leads

# the verdict v, a Lead read as w
def dir_lead_as(v: Dr.Verdict, +w: Dr.Verdict) -> Dr.Verdict:
  match v:
    case Dr.Defer{}:
      Dr.Defer{}
    case Dr.Again{}:
      Dr.Again{}
    case Dr.Yield{}:
      Dr.Yield{}
    case Dr.Stack{l}:
      Dr.Stack{l}
    case Dr.Leave{}:
      Dr.Leave{}
    case Dr.Abort{}:
      Dr.Abort{}
    case Dr.Lead{}:
      w

# the verdicts vs, every Lead read as w
def dir_leads(vs: List<&2, Dr.Verdict>, +w: Dr.Verdict) -> List<&2, Dr.Verdict>:
  match vs:
    case Nil{}:
      Nil{}
    case v <> rest:
      dir_lead_as(v, w) <> dir_leads(rest, w)

# LAW: a step that goes on is the step where every layer that leads
# leaves
law dir_lead_leaves_with_the_continuation:
  for +cap: Nat
  for +l: Dr.Loop
  for +vs: List<&2, Dr.Verdict>
  for on: {Dr.ended(Dr.tick(cap, l, dir_leads(vs, Dr.Leave{}))) == False{} : Bool}
  {Dr.tick(cap, l, vs) == Dr.tick(cap, l, dir_leads(vs, Dr.Leave{})) : Dr.Loop}

# LAW: a step that ends the loop is the step where every layer that leads
# stays (defers): a reminder never leaves without its continuation
law dir_lead_stays_when_the_loop_ends:
  for +cap: Nat
  for +l: Dr.Loop
  for +vs: List<&2, Dr.Verdict>
  for ends: {Dr.ended(Dr.tick(cap, l, dir_leads(vs, Dr.Leave{}))) == True{} : Bool}
  {Dr.tick(cap, l, vs) == Dr.tick(cap, l, dir_leads(vs, Dr.Defer{})) : Dr.Loop}

# LAW: anchor: a reminder over a goal with budget leads the goal's
# continuation and leaves with it
law dir_lead_goes_example:
  {Dr.tick(4n, Dr.Loop{3n, [Dr.Layer{2n, 0n}, Dr.Layer{0n, 5n}], None{}}, [Dr.Lead{}, Dr.Again{}]) == Dr.Loop{2n, [Dr.Layer{0n, 4n}], None{}} : Dr.Loop}

# LAW: anchor: a reminder over a goal that yields stays for the next run
law dir_lead_stays_example:
  {Dr.tick(4n, Dr.Loop{3n, [Dr.Layer{2n, 0n}, Dr.Layer{0n, 5n}], None{}}, [Dr.Lead{}, Dr.Yield{}]) == Dr.Loop{3n, [Dr.Layer{2n, 0n}, Dr.Layer{0n, 5n}], Some{Dr.Hand{}}} : Dr.Loop}

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

# LAW: with no cap every tool keeps its strict schema
law strict_no_cap:
  for +ts: List<&2, If.Tool>
  {If.strict.of(None{}, ts) == (ts, []) : List<&2, If.Tool> & List<&2, If.Tool>}

# LAW: a request's cap splits the tools as strict does, so
# strict_within_cap, strict_keeps_every_tool and strict_by_priority hold
# for every request
law strict_cap_is_strict:
  for +c: Nat
  for +ts: List<&2, If.Tool>
  {If.strict.of(Some{c}, ts) == If.strict(c, ts) : List<&2, If.Tool> & List<&2, If.Tool>}

# the ids of the tools of ts, in order
def strict.ids(ts: List<&2, If.Tool>) -> List<&2, Nat>:
  match ts:
    case Nil{}:
      Nil{}
    case t <> rest:
      If.Tool.id(t) <> strict.ids(rest)

# LAW: a plan that fits lists exactly the loose tools of the request
law plan_fits_lists_the_loose:
  for cap: Maybe<&2, Nat>
  for +ts: List<&2, If.Tool>
  for +need: List<&2, Nat>
  for +ls: List<&2, Nat>
  for f: {If.plan(cap, ts, need) == If.Fits{ls} : If.Plan}
  {ls == strict.ids(Pair.snd(List<&2, If.Tool>, List<&2, If.Tool>, If.strict.of(cap, ts))) : List<&2, Nat>}

# LAW: a tool that requires a strict schema is never sent loose
# EXCLUDES: a request that drops the schema a tool requires
law plan_never_loosens_a_needed_tool:
  for cap: Maybe<&2, Nat>
  for +ts: List<&2, If.Tool>
  for +need: List<&2, Nat>
  for +ls: List<&2, Nat>
  for +i: Nat
  for +f: {If.plan(cap, ts, need) == If.Fits{ls} : If.Plan}
  for +n: {If.elem(need, i) == True{} : Bool}
  {If.elem(ls, i) == False{} : Bool}

# LAW: a refusal names a tool that requires a strict schema and is past
# the cap; EXCLUDES: refusing a request that fits
# LEAVES FREE: which such tool it names when there are several (the
# model names the first loose one, highest priority first)
law plan_refusal_names_a_needed_loose_tool:
  for cap: Maybe<&2, Nat>
  for +ts: List<&2, If.Tool>
  for +need: List<&2, Nat>
  for +i: Nat
  for o: {If.plan(cap, ts, need) == If.Over{i} : If.Plan}
  {Bool.and(If.elem(need, i), If.elem(strict.ids(Pair.snd(List<&2, If.Tool>, List<&2, If.Tool>, If.strict.of(cap, ts))), i)) == True{} : Bool}

# LAW: a required tool past the cap refuses the request (witness of the
# refusal)
law plan_example_over:
  {If.plan(Some{1n}, [If.Tool{0n, 1n}, If.Tool{1n, 3n}, If.Tool{2n, 2n}], [0n, 2n]) == If.Over{2n} : If.Plan}

# LAW: a required tool within the cap fits (witness of a fit)
law plan_example_fits:
  {If.plan(Some{1n}, [If.Tool{0n, 1n}, If.Tool{1n, 3n}, If.Tool{2n, 3n}], [1n]) == If.Fits{[2n, 0n]} : If.Plan}

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

# spec: the first of the three checks that passes picks the frame drawn
# (the frame f, its full redraw g, its fresh redraw h on a blank screen);
# when none passes nothing is drawn and the first frame is kept
def screen_paint_spec(f: Nat, g: Nat, h: Nat, ok1: Bool, ok2: Bool, ok3: Bool) -> Sc.Paint:
  match ok1:
    case True{}:
      Sc.Put{f, False{}}
    case False{}:
      match ok2:
        case True{}:
          Sc.Put{g, True{}}
        case False{}:
          match ok3:
            case True{}:
              Sc.Fresh{h}
            case False{}:
              Sc.Kept{f}

# LAW: the screen never stops: the first check that passes picks what
# reaches the terminal (the frame, its full redraw, its fresh redraw on a
# blank screen); when all three fail nothing is drawn, the first frame is
# kept, and the surface goes on
# EXCLUDES: a frame drawn after its check failed; a passing redraw left
# unused; a fresh redraw before both checks failed; an end of the surface
# (or any outcome but Kept) after three failed checks
law paint_first_passing_check:
  for +f: Nat
  for +g: Nat
  for +h: Nat
  for +ok1: Bool
  for +ok2: Bool
  for +ok3: Bool
  {Sc.resync(Sc.present(f, g, ok1, ok2), h, ok3) == screen_paint_spec(f, g, h, ok1, ok2, ok3) : Sc.Paint}

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

# maxToolRounds, the ms a deferred job may run (a poll spends 1 ms),
# retry.maxRetries, MAX_NOTES and one

# ---- release ----

# LAWS (R1): eukhe's release versions. Each law is an open claim about
# the model in bend/semver.bend; PROOF.bend proves them (as Laws.<law>)
# with the lemmas of PROOF.bend section semver.

# (R1) Release versions
# ---------------------
# docs/develop.md "Releases", the model in bend/semver.bend; the script
# scripts/release/next_version.py implements it and its bridge test runs
# both on the same cases. Every input is free: any version, any tags (any
# text, in any order: other series, other prefixes, no version at all),
# any workspace version.

# LAW: reading a written version gives it back
law semver_roundtrip:
  for v: Sv.Ver
  {Sv.Ver.parse(Sv.Ver.show(v)) == Some{v} : Maybe<&2, Sv.Ver>}

# LAW: the order is reflexive
law semver_le_refl:
  for v: Sv.Ver
  {Sv.Ver.le(v, v) == True{} : Bool}

# LAW: the order is antisymmetric
law semver_le_antisym:
  for u: Sv.Ver
  for v: Sv.Ver
  for uv: {Sv.Ver.le(u, v) == True{} : Bool}
  for vu: {Sv.Ver.le(v, u) == True{} : Bool}
  {u == v : Sv.Ver}

# LAW: the order is transitive
law semver_le_trans:
  for u: Sv.Ver
  for v: Sv.Ver
  for w: Sv.Ver
  for uv: {Sv.Ver.le(u, v) == True{} : Bool}
  for vw: {Sv.Ver.le(v, w) == True{} : Bool}
  {Sv.Ver.le(u, w) == True{} : Bool}

# LAW: the order is total
law semver_le_total:
  for u: Sv.Ver
  for v: Sv.Ver
  {Bool.or(Sv.Ver.le(u, v), Sv.Ver.le(v, u)) == True{} : Bool}

# LAW: the next release is newer than every tag of its series
law semver_next_newer:
  for s: Sv.Ver
  for +xs: List<&2, String>
  for +t: String
  for +ys: List<&2, String>
  for v: Sv.Ver
  for parsed: {Sv.Tag.ver(t) == Some{v} : Maybe<&2, Sv.Ver>}
  for ins: {Sv.Ver.in_series(s, v) == True{} : Bool}
  {Sv.Ver.lt(v, Sv.Rel.next(s, List.append(&2, String, xs, t <> ys))) == True{} : Bool}

# LAW: the next release is no version a tag names, of any series
law semver_next_not_tagged:
  for +s: Sv.Ver
  for +xs: List<&2, String>
  for +t: String
  for +ys: List<&2, String>
  for +v: Sv.Ver
  for parsed: {Sv.Tag.ver(t) == Some{v} : Maybe<&2, Sv.Ver>}
  {v != Sv.Rel.next(s, List.append(&2, String, xs, t <> ys)) : Sv.Ver}

# LAW: the tag of the next release is none of the tags
law semver_next_tag_new:
  for +s: Sv.Ver
  for +xs: List<&2, String>
  for +t: String
  for +ys: List<&2, String>
  {Sv.Tag.of(Sv.Rel.next(s, List.append(&2, String, xs, t <> ys))) != t : String}

# LAW: a series with no tag starts at patch 0
law semver_fresh_series:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +tags: List<&2, String>
  for none: {Sv.Rel.none(Sv.Ver{a, b, c}, tags) == True{} : Bool}
  {Sv.Rel.next(Sv.Ver{a, b, c}, tags) == Sv.Ver{a, b, 0n} : Sv.Ver}

# LAW: a tag that names no version of the series does not change the
# next release
law semver_other_series:
  for s: Sv.Ver
  for +xs: List<&2, String>
  for +t: String
  for +ys: List<&2, String>
  for other: {Sv.Rel.ofs(s, t) == False{} : Bool}
  {Sv.Rel.next(s, List.append(&2, String, xs, t <> ys)) == Sv.Rel.next(s, List.append(&2, String, xs, ys)) : Sv.Ver}

# LAW: the release of v is titled `Eukhe v` ++ show(v)
law semver_title:
  for v: Sv.Ver
  {Sv.Rel.title(v) == String.append("Eukhe v", Sv.Ver.show(v)) : String}

# LAW: the tag of v names v
law semver_tag_roundtrip:
  for v: Sv.Ver
  {Sv.Tag.ver(Sv.Tag.of(v)) == Some{v} : Maybe<&2, Sv.Ver>}

# LAW: a release is newer than every version tag, of any series
law semver_release_newest:
  for c: String
  for +xs: List<&2, String>
  for +t: String
  for +ys: List<&2, String>
  for r: Sv.Ver
  for rel: {Sv.Rel.release(c, List.append(&2, String, xs, t <> ys)) == Some{r} : Maybe<&2, Sv.Ver>}
  for +v: Sv.Ver
  for parsed: {Sv.Tag.ver(t) == Some{v} : Maybe<&2, Sv.Ver>}
  {Sv.Ver.lt(v, r) == True{} : Bool}

# LAW: with the workspace version X.Y.0 and no version tag of another
# series, the release is the next release of X.Y
law semver_release_progress:
  for c: String
  for +a: Nat
  for +b: Nat
  for +tags: List<&2, String>
  for parsed: {Sv.Ver.parse(c) == Some{Sv.Ver{a, b, 0n}} : Maybe<&2, Sv.Ver>}
  for only: {Sv.Rel.only(Sv.Ver{a, b, 0n}, tags) == True{} : Bool}
  {Sv.Rel.release(c, tags) == Some{Sv.Rel.next(Sv.Ver{a, b, 0n}, tags)} : Maybe<&2, Sv.Ver>}

# LAW: a workspace version X.Y.(1+z) gives no release, with any tags
# EXCLUDES: a workspace version that is no series start (0.10.3 instead of
# 0.10.0) releases anyway; a release whose number ignores the workspace
# version's patch
# LEAVES FREE: the error the script prints
law semver_release_refuses_patch_workspace:
  for c: String
  for +a: Nat
  for +b: Nat
  for +z: Nat
  for +tags: List<&2, String>
  for parsed: {Sv.Ver.parse(c) == Some{Sv.Ver{a, b, 1n+z}} : Maybe<&2, Sv.Ver>}
  {Sv.Rel.release(c, tags) == None{} : Maybe<&2, Sv.Ver>}

# LAW: a workspace version that is no version gives no release, with any
# tags
# EXCLUDES: a broken Cargo.toml version ("0.10", "0.10.0-dev", "") falls
# back to a default series and releases
# LEAVES FREE: the error the script prints
law semver_release_refuses_unparsed_workspace:
  for c: String
  for +tags: List<&2, String>
  for unparsed: {Sv.Ver.parse(c) == None{} : Maybe<&2, Sv.Ver>}
  {Sv.Rel.release(c, tags) == None{} : Maybe<&2, Sv.Ver>}

# LAW: the premise of semver_release_refuses_patch_workspace holds for a
# real text: "0.10.1" reads as 0.10.1
# EXCLUDES: a refusal law that holds only because no text ever parses to
# a patch above 0
law semver_parse_patch_example:
  {Sv.Ver.parse("0.10.1") == Some{Sv.Ver{0n, 10n, 1n}} : Maybe<&2, Sv.Ver>}

# LAW: the premise of semver_release_refuses_unparsed_workspace holds for
# a real text: "0.10" is no version
# EXCLUDES: a refusal law that holds only because every text parses
law semver_parse_two_fields_example:
  {Sv.Ver.parse("0.10") == None{} : Maybe<&2, Sv.Ver>}

# The decimal writer of the spec, independent of the model: a number's
# text is the text of the number before it with its last digit raised,
# a 9 becoming 0 and carrying left. It works on the text written last
# digit first, so the carry walks from the head.

def dec_pick(b: Bool, yes: Char, no: Char) -> Char:
  match b:
    case True{}:
      yes
    case False{}:
      no

# the digit after c ('0' to '8'); any other char stays
def dec_succ(+c: Char) -> Char:
  dec_pick(Char.is_eq(c, '0'), '1', dec_pick(Char.is_eq(c, '1'), '2', dec_pick(Char.is_eq(c, '2'), '3', dec_pick(Char.is_eq(c, '3'), '4', dec_pick(Char.is_eq(c, '4'), '5', dec_pick(Char.is_eq(c, '5'), '6', dec_pick(Char.is_eq(c, '6'), '7', dec_pick(Char.is_eq(c, '7'), '8', dec_pick(Char.is_eq(c, '8'), '9', c)))))))))

# the digit c raised: a 9 becomes 0 and the raised rest follows it;
# any other digit becomes the next one and the rest stays
def dec_raise_at(nine: Bool, c: Char, r: String, raised: String) -> String:
  match nine:
    case True{}:
      SCon{'0', raised}
    case False{}:
      SCon{dec_succ(c), r}

# the text, last digit first, of the number after the one s writes
def dec_raise(s: String) -> String:
  match s:
    case SNil{}:
      SCon{'1', SNil{}}
    case SCon{+c, +r}:
      dec_raise_at(Char.is_eq(c, '9'), c, r, dec_raise(r))

# n in decimal, most significant digit first, no leading zero
def dec_spec(n: Nat) -> String:
  match n:
    case 0n:
      SCon{'0', SNil{}}
    case 1n+p:
      String.reverse(dec_raise(String.reverse(dec_spec(p))))

# LAW: a version is written as its three numbers in decimal, most
# significant digit first, joined by dots
# EXCLUDES: digits written in reverse ("0.01.24" for 0.10.42) by a writer
# that its reader undoes, which semver_roundtrip alone lets pass; a
# leading zero; fields in another order or with another separator
law semver_show_decimal:
  for a: Nat
  for b: Nat
  for c: Nat
  {Sv.Ver.show(Sv.Ver{a, b, c}) == String.append(dec_spec(a), SCon{'.', String.append(dec_spec(b), SCon{'.', dec_spec(c)})}) : String}

# LAW: the spec's writer is decimal: 109 is "109"
# EXCLUDES: a spec writer that is wrong past one digit or past a carry
law semver_dec_spec_example:
  {dec_spec(109n) == "109" : String}

# ---- auth_flight ----

# LAWS (A1): the OAuth refresh flight. Each law is an open claim about the
# model in bend/auth_flight.bend; PROOF.bend proves them (as
# Laws.<law>) with the lemmas of PROOF.bend section auth_flight.

# (A1) One refresh flight per provider
# ------------------------------------
# The OAuth refresh of an expired stored credential
# (crates/eukhe-core/src/auth/flight.rs): the callers of one provider share
# one token fetch. The bridge test crates/eukhe-core/src/auth/flight/bridge.rs
# runs the Rust state machine and the model on the same interleavings.
# Every input is free: any callers, their steps in any order, any fetch
# results, peer writes and expiries at any time.

# LAW: at most one fetch is in flight
law flight_one_fetch:
  for +evs: List<&2, F.Ev>
  {F.le(F.fetching(F.St.cs(F.run(evs))), 1n) == True{} : Bool}

# LAW: a caller that boards while flight f is in flight (caller j leads
# it) joins flight f
law flight_board_joins:
  for +evs: List<&2, F.Ev>
  for +j: Nat
  for +lj: F.Leg
  for +f: Nat
  for leads: {List.get(&2, F.Leg, F.St.cs(F.run(evs)), j) == Some{lj} : Maybe<&2, F.Leg>}
  for flight: {F.led(lj) == Some{f} : Maybe<&2, Nat>}
  for +k: Nat
  for +ok: Bool
  for boards: {List.get(&2, F.Leg, F.St.cs(F.run(evs)), k) == Some{F.Board{}} : Maybe<&2, F.Leg>}
  {List.get(&2, F.Leg, F.St.cs(F.step(F.run(evs), F.Step{k, ok})), k) == Some{F.Waiting{f}} : Maybe<&2, F.Leg>}

# LAW: every caller of flight f (its leader, and each caller that joined
# it) gets the outcome flight f landed with
law flight_callers_get_its_outcome:
  for +evs: List<&2, F.Ev>
  for +k: Nat
  for +f: Nat
  for +o: F.Out
  for served: {List.get(&2, F.Leg, F.St.cs(F.run(evs)), k) == Some{F.Served{Some{f}, o}} : Maybe<&2, F.Leg>}
  {List.get(&2, F.Out, F.W.landed(F.St.w(F.run(evs))), f) == Some{o} : Maybe<&2, F.Out>}

# LAW: a caller that joined flight f takes its outcome at its next step
# once flight f landed
law flight_landed_serves:
  for +s: F.St
  for +k: Nat
  for +f: Nat
  for +o: F.Out
  for +ok: Bool
  for waits: {List.get(&2, F.Leg, F.St.cs(s), k) == Some{F.Waiting{f}} : Maybe<&2, F.Leg>}
  for landed: {List.get(&2, F.Out, F.W.landed(F.St.w(s)), f) == Some{o} : Maybe<&2, F.Out>}
  {List.get(&2, F.Leg, F.St.cs(F.step(s, F.Step{k, ok})), k) == Some{F.Served{Some{f}, o}} : Maybe<&2, F.Leg>}

# LAW: a flight ends after its credential is stored: once caller k lands
# flight f with credential c, the store holds c or a newer credential, so a
# caller after the end sees the stored credential
law flight_after_end_stored:
  for +evs: List<&2, F.Ev>
  for +k: Nat
  for +f: Nat
  for +c: Nat
  for lands: {List.get(&2, F.Leg, F.St.cs(F.run(evs)), k) == Some{F.Land{f, F.Ok{c}}} : Maybe<&2, F.Leg>}
  for +ok: Bool
  {F.le(c, F.Sto.c(F.W.sto(F.St.w(F.step(F.run(evs), F.Step{k, ok}))))) == True{} : Bool}

# LAW: a caller after the end sees the stored credential: once caller k
# lands flight f with credential c, a caller that arrives while the store
# is fresh is served the stored credential, c or a newer one
law flight_after_end_served:
  for +evs: List<&2, F.Ev>
  for +k: Nat
  for +f: Nat
  for +c: Nat
  for lands: {List.get(&2, F.Leg, F.St.cs(F.run(evs)), k) == Some{F.Land{f, F.Ok{c}}} : Maybe<&2, F.Leg>}
  for +ok: Bool
  for +ok2: Bool
  for fresh: {F.Sto.fresh(F.W.sto(F.St.w(F.step(F.run(evs), F.Step{k, ok})))) == True{} : Bool}
  F.After(c, F.step(F.run(evs), F.Step{k, ok}), ok2)

# ---- themes ----

# LAWS (T1): themes. Each law is an open claim about the models in
# bend/theme.bend and bend/color.bend; PROOF.bend proves them (as
# Laws.<law>) with the lemmas of PROOF.bend section themes.

# (T1) Themes
# -----------
# docs/interface.md "Themes", the model in bend/theme.bend: the one theme
# validator and name resolver of crates/eukhe-theme, which the terminal UI
# and the HTML export share. Every input is free: any registered, builtin
# and custom candidates in any order, valid or not; any name; any theme
# file (any colors, variables and export page). The shipped themes are
# the tables of bend/theme.bend; the bridge test
# crates/eukhe-core/src/export_html/theme_bridge.rs checks that they equal
# crates/eukhe-theme/themes/*.json and that the Rust code and the model
# agree on generated files, names and colors.

# LAW: the empty name resolves to the default theme, with no warning
law theme_resolve_empty:
  for src: List<&2, T.Cand>
  {T.resolve.name(src, "") == T.Res{T.dflt(), False{}} : T.Res}

# LAW: a name resolves to the first valid theme that advertises it, with
# no warning: a registered file before a builtin before a custom file
law theme_resolve_first:
  for +pre: List<&2, T.Cand>
  for +nm: String
  for +id: U32
  for +post: List<&2, T.Cand>
  for +n: String
  for ne: {String.is_empty(n) == False{} : Bool}
  for miss: {T.hit(pre, n) == False{} : Bool}
  for same: {String.eq(nm, n) == True{} : Bool}
  {T.resolve.name(List.append(&2, T.Cand, pre, T.Cand{nm, True{}, id} <> post), n) == T.Res{id, False{}} : T.Res}

# LAW: a name that no valid theme advertises (missing, or only in invalid
# files) resolves to the default theme, with a warning: resolution never
# fails
law theme_resolve_missing:
  for +src: List<&2, T.Cand>
  for +n: String
  for ne: {String.is_empty(n) == False{} : Bool}
  for miss: {T.hit(src, n) == False{} : Bool}
  {T.resolve.name(src, n) == T.Res{T.dflt(), True{}} : T.Res}

# LAW: a theme file loads only when it is valid (every color resolves and
# every required token is written)
law theme_load_valid:
  for r: T.RFile
  for -f: T.Th
  for loaded: {T.load(r) == Some{f} : Maybe<&2, T.Th>}
  {T.valid(f) == True{} : Bool}

# LAW: the palette of a valid theme file defines every token
law theme_tokens_complete:
  for f: T.Th
  for v: {T.valid(f) == True{} : Bool}
  {T.complete(T.palette(f)) == True{} : Bool}

# LAW: two theme files with the same background have the same mode, light
# or dark
law theme_mode_background:
  for f: T.Th
  for g: T.Th
  for same: {T.bg(f) == T.bg(g) : Co.Rgb}
  {T.light(f) == T.light(g) : Bool}

# LAW: the name of a theme file never changes its palette
law theme_palette_name_free:
  for f: T.Th
  for n: String
  {T.palette(T.rename(f, n)) == T.palette(f) : List<&2, Maybe<&2, T.Val>>}

# LAW: the name of a theme file never changes its mode
law theme_mode_name_free:
  for f: T.Th
  for n: String
  {T.light(T.rename(f, n)) == T.light(f) : Bool}

# LAW: in every shipped theme, every ink token meets its WCAG contrast:
# text 4.5:1, non-text parts 3:1, as exact rationals
law theme_shipped_legible:
  for s: T.Shipped
  {T.legible(T.table(s)) == True{} : Bool}

# LAW: in every shipped theme, the status colors (accent, success,
# warning, error) stay pairwise distinct in a 256-color terminal
law theme_shipped_status_distinct:
  for s: T.Shipped
  {T.status_distinct(T.table(s)) == True{} : Bool}

# ---- dashboard_tokens ----

# LAWS (T2): the dashboard's presentation tokens. Each law is an open
# claim about the model in bend/tokens.bend; PROOF.bend proves them (as
# Laws.<law>) with the lemmas of PROOF.bend section tokens.

# (T2) Dashboard tokens
# ---------------------
# docs/dashboard.md "Tokens", the model in bend/tokens.bend. The web app
# writes every presentation value once, in
# crates/eukhe-dashboard/ui/src/tokens.stylex.ts; its test
# src/tokens.test.ts checks that the token values there equal the tables
# of bend/tokens.bend (through bend/bridge_tokens.bend).

# LAW: every color token has a value in both modes, light and dark
law tokens_paired:
  for t: Tk.Tone
  for m: Tk.Mode
  {Maybe.is_some(&2, Tk.Col, Tk.find(t, Tk.palette(m))) == True{} : Bool}

# LAW: in both modes, every text pair meets the contrast it needs (4.5:1
# for text, 3:1 for a caption on a fill), as exact rationals
law tokens_legible:
  for m: Tk.Mode
  for +pre: List<&2, Tk.Ink>
  for p: Tk.Ink
  for +post: List<&2, Tk.Ink>
  for split: {Tk.pairs() == List.append(&2, Tk.Ink, pre, p <> post) : List<&2, Tk.Ink>}
  {Tk.readable(m, p) == True{} : Bool}

# LAW: the stacking layers are strictly ordered, bottom to top
law tokens_layers_ordered:
  {Tk.ascends(Tk.layers()) == True{} : Bool}

# LAW: the spacing scale strictly ascends
law tokens_space_ascends:
  {Tk.ascends(Tk.space()) == True{} : Bool}

# LAW: the type sizes strictly ascend, and so do the line heights
law tokens_type_ascends:
  {Bool.and(Tk.ascends(Tk.sizes()), Tk.ascends(Tk.lines())) == True{} : Bool}

# ---- progress ----

# LAWS (audit H6, H7, M5, L5): when the harness checks a loop, progress
# is new work, a loop of the same work stops in time, and what the harness
# changes or drops on its own reaches the user. Each law is an open claim
# about the models in bend/progress.bend (and bend/child.bend for the
# subagent watch); PROOF.bend proves them (as Laws.<law>) with the lemmas of
# PROOF.bend section progress.

# (H7) A subagent's progress is new work
# --------------------------------------
# The child's progress token is the work of its acts (Pr.work: its
# distinct tool calls with their results, and its accepted progress
# notes), so events alone (streamed deltas, retries, answers) are no
# progress. The watch of bend/child.bend reads the token.

# LAW: acts the session did before add no work: a child that repeats the
# same calls with the same results keeps its token
law child_repeat_is_no_work:
  for +seen: List<&2, Nat>
  for +loop: List<&2, Nat>
  for within: Pr.Within(loop, seen)
  {Pr.work(List.append(&2, Nat, seen, loop)) == Pr.work(seen) : Nat}

# LAW: a child that loops is a stall: polls of a child whose acts since
# the watch last saw progress are all acts it did before, at least as many
# as the ms left on the clock, end the watch (each poll takes 1 ms or more)
law child_loop_is_a_stall:
  for +cfg: Ch.Cfg
  for +w: Ch.W
  for +hist: List<&2, Nat>
  for p: Pr.Peek
  for +ps: List<&2, Pr.Peek>
  for loops: Pr.Loops(p <> ps, hist)
  for tok: {Ch.W.tok(w) == Some{Pr.work(hist)} : Maybe<&2, Nat>}
  for long: {Nat.is_le(Ch.W.left(w), List.length(&2, Pr.Peek, p <> ps)) == True{} : Bool}
  {Ch.Next.watching(Pr.watch(p <> ps, cfg, hist, Ch.Watch{w})) == False{} : Bool}

# LAW: new work is progress: a poll after an act the child never did
# before goes on with a full clock
law child_new_work_is_progress:
  for +cfg: Ch.Cfg
  for +w: Ch.W
  for +e: Nat
  for +seen: List<&2, Nat>
  for +seg: List<&2, Nat>
  for +x: Nat
  for fresh: {Pr.mem(x, seen) == False{} : Bool}
  for news: Pr.In(x, seg)
  for tok: {Ch.W.tok(w) == Some{Pr.work(seen)} : Maybe<&2, Nat>}
  {Ch.look(cfg, w, e, Ch.Busy{Some{Pr.work(List.append(&2, Nat, seen, seg))}}) == Ch.Watch{Ch.W.fresh(cfg, Some{Pr.work(List.append(&2, Nat, seen, seg))})} : Ch.Next}

# (H6) A goal without progress stops
# ----------------------------------
# At each goal continuation the progress check asks whether the work grew
# since the last continuation (Pr.check, cap: directors.stallSteps).

# LAW: continuations in a row whose acts are all acts the session did
# before, at least as many as the cap, stop the goal, whatever count of
# stalls it starts from
law goal_stops_without_progress:
  for +cap: Nat
  for +s: Nat
  for +hist: List<&2, Nat>
  for +seg: List<&2, Nat>
  for +segs: List<&2, List<&2, Nat>>
  for repeats: Pr.Repeats(seg <> segs, hist)
  for long: {Nat.is_le(cap, List.length(&2, List<&2, Nat>, seg <> segs)) == True{} : Bool}
  {Pr.Goal.stopped(Pr.goal(seg <> segs, cap, hist, Pr.Go{s})) == True{} : Bool}

# LAW: a continuation with an act the session never did before clears
# the count: the goal goes on
law goal_progress_continues:
  for +cap: Nat
  for +s: Nat
  for +hist: List<&2, Nat>
  for +seg: List<&2, Nat>
  for +x: Nat
  for fresh: {Pr.mem(x, hist) == False{} : Bool}
  for news: Pr.In(x, seg)
  {Pr.check(cap, s, Pr.grew(hist, seg)) == Pr.Go{0n} : Pr.Goal}

# The check the Rust goal loop runs (bend/progress.bend `judge`): it
# compares the ledger's counts, and holds the count of stalls below t
# (t = 10^14 - 1, the largest Nat the core's wire carries). Every law
# holds for every t.

# LAW: the first check of a run or a goal starts the count
law goal_first_check_starts:
  for +t: Nat
  for +cap: Nat
  for +work: Nat
  {Pr.judge(t, cap, None{}, work) == Pr.Go{0n} : Pr.Goal}

# LAW: below t, a later check is the progress check on whether the
# work's count grew
law goal_judge_is_check:
  for +t: Nat
  for +cap: Nat
  for +s: Nat
  for +w: Nat
  for +work: Nat
  for below: {Nat.is_lt(s, t) == True{} : Bool}
  {Pr.judge(t, cap, Some{Pr.Prior{s, w}}, work) == Pr.check(cap, s, Nat.is_lt(w, work)) : Pr.Goal}

# LAW: the count grew exactly when the session did new work, so the goal
# laws above hold for the counts the Rust loop compares
law goal_judge_counts_work:
  for +hist: List<&2, Nat>
  for +seg: List<&2, Nat>
  {Nat.is_lt(Pr.work(hist), Pr.work(List.append(&2, Nat, hist, seg))) == Pr.grew(hist, seg) : Bool}

# LAW: the count of stalls stays within t
# EXCLUDES: a count past the compiled core's Nat range (the process stops)
law goal_judge_held:
  for +u: Nat
  for +cap: Nat
  for p: Maybe<&2, Pr.Prior>
  for +work: Nat
  {Nat.is_le(Pr.Goal.stalls(Pr.judge(1n+u, cap, p, work)), 1n+u) == True{} : Bool}

# LAW: a count at t stops a goal with a cap within t that did no new work
# EXCLUDES: a held count that never reaches the cap
law goal_judge_top_stops:
  for +u: Nat
  for +cap: Nat
  for +w: Nat
  for +work: Nat
  for fits: {Nat.is_le(cap, 1n+u) == True{} : Bool}
  for same: {Nat.is_lt(w, work) == False{} : Bool}
  {Pr.judge(1n+u, cap, Some{Pr.Prior{1n+u, w}}, work) == Pr.Stop{1n+u} : Pr.Goal}

# (M5) A model the harness substitutes is reported
# ------------------------------------------------
# bend/aux_fallback.bend: the routing of a background summary pass
# through the `auxiliaryModel` setting (`decide_auxiliary_route`) and the
# session's notices (`run`): a pass with a set selector that differs from
# the session model and cannot be used runs on the session model, and the
# user sees a notice row, once per purpose, selector and reason.

# LAW: every substitution of the session model for a set auxiliary
# selector has a notice
law fallback_is_reported:
  for ps: List<&2, Af.Pass>
  for +k: Af.Key
  for h: {Af.listed(Af.subs(Af.run(ps)), k) == True{} : Bool}
  {Af.listed(Af.notes(Af.run(ps)), k) == True{} : Bool}

# LAW: a notice comes only from a substitution
law fallback_quiet_when_routed:
  for ps: List<&2, Af.Pass>
  for +k: Af.Key
  for h: {Af.listed(Af.notes(Af.run(ps)), k) == True{} : Bool}
  {Af.listed(Af.subs(Af.run(ps)), k) == True{} : Bool}

# LAW: an unset selector runs on the session model with no notice
law fallback_quiet_when_unset:
  for p: Nat
  for ok: Bool
  for look: Af.Look
  for need: Nat
  {Af.decide(Af.Pass{p, Af.Unset{}, ok, look, need}) == Af.Session{} : Af.Route}

# LAW: a selector that names the session model runs on it with no notice
law fallback_quiet_when_same:
  for p: Nat
  for ok: Bool
  for look: Af.Look
  for need: Nat
  {Af.decide(Af.Pass{p, Af.Same{}, ok, look, need}) == Af.Session{} : Af.Route}

# The Rust resolver asks the gate (Af.gate) first, runs the lookups only
# when the gate asks for them, then settles the route (Af.settle); it
# shows, pass by pass, the events of Af.put and keeps the keys of
# Af.after. The laws below pin that protocol to the session's model.

# LAW: a pass's route is its gate settled with its lookups
# EXCLUDES: a resolver whose two steps decide otherwise than the model
law fallback_gate_then_settle:
  for p: Nat
  for sel: Af.Sel
  for ok: Bool
  for look: Af.Look
  for need: Nat
  {Af.decide(Af.Pass{p, sel, ok, look, need}) == Af.settle(Af.gate(p, sel, ok), look, need) : Af.Route}

# LAW: a gate that decided reads nothing the lookups found, so they need
# not run
# EXCLUDES: a route that depends on lookups the resolver skipped
law fallback_known_needs_no_lookup:
  for r: Af.Route
  for look: Af.Look
  for need: Nat
  {Af.settle(Af.Known{r}, look, need) == r : Af.Route}

# LAW: a set, different selector that allowedModels admits is looked up;
# one it does not admit falls back with the reason 0 (not allowed)
# EXCLUDES: lookups for a disallowed model, a disallowed model run, a
#   wrong reason
law fallback_gate_other:
  for p: Nat
  for s: Nat
  {(Af.gate(p, Af.Other{s}, True{}), Af.gate(p, Af.Other{s}, False{})) == (Af.Lookup{p, s}, Af.Known{Af.Fallback{Af.K{p, s, 0n}}}) : Af.Gate & Af.Gate}

# LAW: an unset or same selector keeps the session model without a
# lookup
# EXCLUDES: lookups (credential reads) for a pass that runs on the
#   session model
law fallback_gate_session:
  for p: Nat
  for ok: Bool
  {(Af.gate(p, Af.Unset{}, ok), Af.gate(p, Af.Same{}, ok)) == (Af.Known{Af.Session{}}, Af.Known{Af.Session{}}) : Af.Gate & Af.Gate}

# LAW: lookups that find nothing usable fall back with their reason
# EXCLUDES: a lookup failure run anyway, its reason replaced
law fallback_miss_keeps_reason:
  for p: Nat
  for s: Nat
  for r: Nat
  for need: Nat
  {Af.settle(Af.Lookup{p, s}, Af.Miss{r}, need) == Af.Fallback{Af.K{p, s, r}} : Af.Route}

# LAW: a found model whose window is unknown (0) or at least the request
# runs the pass (a window saturated at the wire's largest Nat is at
# least every request)
# EXCLUDES: a fitting model refused, an unknown window read as too small
law fallback_window_fits:
  for p: Nat
  for s: Nat
  for +w: Nat
  for +need: Nat
  for fit: {Bool.or(Nat.is_eq(w, 0n), Nat.is_le(need, w)) == True{} : Bool}
  {Af.settle(Af.Lookup{p, s}, Af.Hit{w}, need) == Af.Routed{} : Af.Route}

# LAW: a found model whose known window is smaller than the request falls
# back with the reason 5 (window too small)
# EXCLUDES: a request sent to a model too small for it
law fallback_window_small:
  for p: Nat
  for s: Nat
  for +w: Nat
  for +need: Nat
  for small: {Nat.is_lt(1n+w, need) == True{} : Bool}
  {Af.settle(Af.Lookup{p, s}, Af.Hit{1n+w}, need) == Af.Fallback{Af.K{p, s, 5n}} : Af.Route}

# LAW: the events of a pass come before the events of the passes after
# it: a session shows each pass's own events in order
# EXCLUDES: a pass whose shown events depend on the passes after it
law fallback_pass_events:
  for r: Af.Route
  for +sh: List<&2, Af.Key>
  for t: List<&2, Af.Ev>
  {Af.put(r, sh, t) == List.append(&2, Af.Ev, Af.put(r, sh, Nil{}), t) : List<&2, Af.Ev>}

# (L5) A skill file that fails to load is reported
# ------------------------------------------------
# bend/skill_load.bend: the skill and prompt-template loaders over their
# candidate files (`load`): each file loads, or a diagnostic names its
# path and error.

# LAW: every candidate file is loaded or named by a diagnostic
law skill_failure_reported:
  for cs: List<&2, Sk.Cand>
  for +c: Sk.Cand
  for i: Sk.In(c, cs)
  {Bool.or(Sk.listed(Sk.loaded(cs), Sk.Cand.path(c)), Sk.listed(Sk.named(Sk.diags(cs)), Sk.Cand.path(c))) == True{} : Bool}

# LAW: of distinct candidates, no file both loads and fails
law skill_loaded_not_failed:
  for cs: List<&2, Sk.Cand>
  for +n: Nat
  for +d: {Sk.distinct(cs) == True{} : Bool}
  {Bool.and(Sk.listed(Sk.loaded(cs), n), Sk.listed(Sk.named(Sk.diags(cs)), n)) == False{} : Bool}

# ---- ladder ----

# LAWS (S6.9): the thinking ladder of a model is rulebook data. Each law
# is an open claim about the model in bend/infer.bend section 6;
# PROOF.bend proves them (as Laws.<law>) with the lemmas of
# PROOF.bend section quirks.

# (S6.9) The thinking ladder
# --------------------------
# docs/inference.md S6.9 and S10 (the ladder 0), the model in
# bend/infer.bend section 6. Every input is free: any explicit map, any
# rulebook ladder, any default ladders, any level.

# LAW: a model's explicit thinking-level map is its chosen ladder, over
# any ladder of the rulebook
law quirk_ladder_explicit_first:
  for +e: Ef.LvMap
  for +rule: Maybe<&2, Ef.LvMap>
  {If.lad.chosen(Some{e}, rule) == e : Ef.LvMap}

# LAW: with no explicit map, the rulebook's ladder is the chosen ladder
law quirk_ladder_rule_second:
  for +l: Ef.LvMap
  {If.lad.chosen(None{}, Some{l}) == l : Ef.LvMap}

# LAW: with no explicit map and no rulebook ladder, the chosen ladder has
# no entry: the default ladder gives every level
law quirk_ladder_default_last:
  {If.lad.chosen(None{}, None{}) == Ef.LvMap.none() : Ef.LvMap}

# LAW: a reasoning model offers a level exactly when its chosen ladder
# gives the level a wire string, or gives it no entry and the default
# ladder lists it; no other path offers a level
law quirk_ladder_offered_exact:
  for +explicit: Maybe<&2, Ef.LvMap>
  for +rule: Maybe<&2, Ef.LvMap>
  for +d: If.Defaults
  for +l: Ef.Lv
  {Ef.has(If.lad.offered(True{}, explicit, rule, d), l) == If.lad.keep(l, Ef.entry(l, If.lad.chosen(explicit, rule)), If.Defaults.reasoning(d)) : Bool}

# LAW: a model without reasoning offers exactly the levels of the plain
# default ladder, whatever its maps
law quirk_ladder_plain_exact:
  for +explicit: Maybe<&2, Ef.LvMap>
  for +rule: Maybe<&2, Ef.LvMap>
  for +d: If.Defaults
  for +l: Ef.Lv
  {Ef.has(If.lad.offered(False{}, explicit, rule, d), l) == Ef.has(If.Defaults.plain(d), l) : Bool}

# LAW: with the shipped default ladders, the levels a model offers are the
# S10 ladder of its chosen map, so every law of S10 holds for them
law quirk_ladder_shipped_is_s10:
  for r: Bool
  for +map: Ef.LvMap
  {If.lad.offered.of(r, map, If.lad.shipped()) == Ef.offered(Ef.Mdl{r, map}) : List<&2, Ef.Lv>}

# the entry is a wire string
def ladder.is_wire(e: Ef.Ent) -> Bool:
  match e:
    case Ef.Missing{}:
      False{}
    case Ef.Null{}:
      False{}
    case Ef.Wire{}:
      True{}

# some level of ls has a wire entry in m
def ladder.wired.go(ls: List<&2, Ef.Lv>, +m: Ef.LvMap) -> Bool:
  match ls:
    case Nil{}:
      False{}
    case l <> rest:
      Bool.or(ladder.is_wire(Ef.entry(l, m)), ladder.wired.go(rest, m))

# an explicit map gives some level a wire string
def ladder.wired(explicit: Maybe<&2, Ef.LvMap>) -> Bool:
  match explicit:
    case Some{+m}:
      ladder.wired.go(Ef.ladder(), m)
    case None{}:
      False{}

# LAW: a model reasons when its flag says so and, for a registry model
# (by_map, #2858), when its explicit map gives some level a wire string;
# no other input makes a model reason
law quirk_ladder_reasons:
  for f: Bool
  for bm: Bool
  for +explicit: Maybe<&2, Ef.LvMap>
  {If.lad.reasons(f, bm, explicit) == Bool.or(f, Bool.and(bm, ladder.wired(explicit))) : Bool}

# LAW: the levels a model offers are the S10 ladder of one model, so the
# S10 laws of the clamp and the cycle hold for every ladder of the
# rulebook, with any default ladders
law quirk_ladder_model_offers:
  for r: Bool
  for +explicit: Maybe<&2, Ef.LvMap>
  for +rule: Maybe<&2, Ef.LvMap>
  for +d: If.Defaults
  {Ef.offered(If.lad.model(r, explicit, rule, d)) == If.lad.offered(r, explicit, rule, d) : List<&2, Ef.Lv>}

# ---- kernel_local ----

# LAWS (K1): the kernel environment is local. A session never downloads;
# `eukhe kernel install` is the only download, and it checks every file
# against its hash before the kernel uses it; a missing kernel never
# blocks the other tools; a bootstrap lock candidate never outlives its
# attempt. Each law is an open claim about the model in
# bend/kernel_local.bend; PROOF.bend proves them (as Laws.<law>)
# with the lemmas of PROOF.bend section kernel_local.

# (K1.1) The setup
# ----------------
# crates/eukhe-core/src/kernel/bootstrap/setup.rs `setup_step` and
# venv.rs `venv_build_commands`. Every input is free: any venv found,
# either setup.

# LAW: a session (any path but `eukhe kernel install`) fetches nothing,
# whatever kernel venv it finds
law kernel_session_never_downloads:
  for f: KL.Found
  {KL.acts.fetching(KL.plan(f, KL.Local{})) == False{} : Bool}

# LAW: a setup that fetches is `eukhe kernel install`
law kernel_download_only_on_install:
  for f: KL.Found
  for s: KL.Setup
  for fetches: {KL.acts.fetching(KL.plan(f, s)) == True{} : Bool}
  {s == KL.Install{} : KL.Setup}

# LAW: every fetch is checked against a pinned hash, and the kernel starts
# only after a check of the venv that came after the last fetch
law kernel_fetch_verified_before_use:
  for f: KL.Found
  for s: KL.Setup
  {KL.acts.verified(KL.plan(f, s), True{}) == True{} : Bool}

# LAW: every setup ends with the kernel started: no setup is a no-op
law kernel_setup_runs:
  for f: KL.Found
  for s: KL.Setup
  {KL.acts.runs(KL.plan(f, s)) == True{} : Bool}

# LAW: an install of a missing or out-of-date venv fetches
law kernel_install_fetches:
  {KL.acts.fetching(KL.plan(KL.Stale{}, KL.Install{})) == True{} : Bool}

# (K1.2) The session's tools
# --------------------------
# crates/eukhe-core/src/kernel/bootstrap/mod.rs `format_setup_failure`
# and the ipython tool (durable/rlm/tool.rs), which answers with the
# kernel's start error.

# LAW: a missing kernel never blocks another tool: it runs whatever the
# setup found and whether the setup worked
law kernel_missing_spares_tools:
  for n: Nat
  for f: KL.Found
  for ok: Bool
  {KL.answer(KL.Other{n}, KL.start(f, ok)) == KL.Ran{} : KL.Answer}

# LAW: when the setup of a venv that is not current fails, the ipython
# tool answers with the install command
law kernel_missing_names_install:
  for f: KL.Found
  for failed: {KL.start(f, False{}) == KL.Missing{} : KL.Kernel}
  {KL.answer(KL.Python{}, KL.start(f, False{})) == KL.NamesInstall{} : KL.Answer}

# (K1.3) The bootstrap lock
# -------------------------
# crates/eukhe-core/src/kernel/bootstrap/dir_lock.rs
# `try_acquire_dir_lock` and `sweep_leftovers`.

# LAW: an attempt on any lock leaves no candidate of its own
law kernel_lock_attempt_leaves_none:
  for l: KL.Lock
  {KL.own_left(KL.attempt(l)) == 0n : Nat}

# LAW: the sweep removes every leftover of a dead attempt (a process that
# died inside its attempt)
law kernel_lock_sweep_removes_dead:
  for ls: List<&2, KL.Left>
  {KL.lefts.dead(KL.sweep(ls)) == 0n : Nat}

# LAW: the sweep keeps every leftover of a live attempt and every other
# file
law kernel_lock_sweep_keeps_live:
  for ls: List<&2, KL.Left>
  {KL.lefts.live(KL.sweep(ls)) == KL.lefts.live(ls) : Nat}

# ---- storage ----

# LAWS (D2): the durable storage of a session. Each law is an open claim
# about the models in bend/log.bend and bend/staging.bend; PROOF.bend
# proves them (as Laws.<law>) with the lemmas of PROOF.bend section log
# and PROOF.bend section staging.

# (D2) Storage
# ------------
# docs/state.md D2. The commit log `main.jsonl` (bend/log.bend): every
# input is free: any disk (any bytes, a torn tail, no file), any commits,
# any crash point, any number of bytes not flushed that the crash keeps,
# and whether the crash drops the directory entries not flushed.

# LAW: open reads exactly the complete lines, in order; a torn tail (the
# bytes after the last newline) is never read as an entry
law log_reads_lines:
  for +ls: List<&2, List<&2, Nat>>
  for +t: List<&2, Nat>
  {Lg.recover(List.append(&2, Nat, Lg.render(ls), Lg.data(t))) == ls : List<&2, List<&2, Nat>>}

# LAW: a crash at any point never loses a commit: after an epoch the log
# is the log before it, then every commit it acknowledged, then maybe more
law log_ack_durable:
  for d: Lg.Disk
  for e: Lg.Epoch
  exs rest: List<&2, List<&2, Nat>>
  {Lg.Disk.log(Lg.after(d, e)) == List.append(&2, List<&2, Nat>, List.append(&2, List<&2, Nat>, Lg.Disk.log(d), Lg.acked(d, e)), rest) : List<&2, List<&2, Nat>>}

# LAW: after an epoch the log is the log before it, then a prefix of the
# commits it tried, in order: nothing torn, nothing out of order, nothing
# twice
law log_only_commits:
  for d: Lg.Disk
  for e: Lg.Epoch
  exs n: Nat
  {Lg.Disk.log(Lg.after(d, e)) == List.append(&2, List<&2, Nat>, Lg.Disk.log(d), List.take(&2, List<&2, Nat>, Lg.Epoch.cs(e), n)) : List<&2, List<&2, Nat>>}

# Staging, sweep and listing (bend/staging.bend): every input is free: any
# directory entries with any names, any nodes a sweep may meet (held or
# not, stale or not, reached or not, of any sort), any sessions directory.

# LAW: a publish to a name that an entry has fails and changes nothing:
# a rename never replaces an existing target, not even an empty directory
law publish_never_overwrites:
  for +s: Nat
  for +t: Nat
  for +es: List<&2, Sg.Entry>
  for taken: {Sg.has(t, es) == True{} : Bool}
  {Sg.publish(s, t, es) == Sg.Pub{False{}, es} : Sg.Pub}

# LAW: a publish to a free name moves the storage
law publish_moves:
  for +s: Nat
  for +t: Nat
  for +es: List<&2, Sg.Entry>
  for free: {Sg.has(t, es) == False{} : Bool}
  {Sg.Pub.ok(Sg.publish(s, t, es)) == True{} : Bool}

# LAW: a sweep never removes an entry a live process holds the lock of
law sweep_never_live:
  for +pre: List<&2, Sg.Node>
  for +i: Nat
  for +k: Sg.Sort
  for +s: Bool
  for +o: Bool
  for +post: List<&2, Sg.Node>
  {Sg.sweep(List.append(&2, Sg.Node, pre, Sg.Node{i, k, True{}, s, o} <> post)) == List.append(&2, Sg.Node, Sg.sweep(pre), Sg.sweep(post)) : List<&2, Sg.Node>}

# LAW: a sweep never removes an entry touched within the day
law sweep_never_young:
  for +pre: List<&2, Sg.Node>
  for +i: Nat
  for +k: Sg.Sort
  for +h: Bool
  for +o: Bool
  for +post: List<&2, Sg.Node>
  {Sg.sweep(List.append(&2, Sg.Node, pre, Sg.Node{i, k, h, False{}, o} <> post)) == List.append(&2, Sg.Node, Sg.sweep(pre), Sg.sweep(post)) : List<&2, Sg.Node>}

# LAW: a sweep never removes an entry it does not reach (inside a storage
# or a leftover, behind a symlink)
law sweep_stays_out:
  for +pre: List<&2, Sg.Node>
  for +i: Nat
  for +k: Sg.Sort
  for +h: Bool
  for +s: Bool
  for +post: List<&2, Sg.Node>
  {Sg.sweep(List.append(&2, Sg.Node, pre, Sg.Node{i, k, h, s, False{}} <> post)) == List.append(&2, Sg.Node, Sg.sweep(pre), Sg.sweep(post)) : List<&2, Sg.Node>}

# LAW: a sweep removes every free, stale leftover it reaches, at any depth
law sweep_reaches_every_depth:
  for +pre: List<&2, Sg.Node>
  for +i: Nat
  for +k: Sg.Sort
  for +post: List<&2, Sg.Node>
  for sw: {Sg.Sort.swept(k) == True{} : Bool}
  {Sg.sweep(List.append(&2, Sg.Node, pre, Sg.Node{i, k, False{}, True{}, True{}} <> post)) == List.append(&2, Sg.Node, Sg.sweep(pre), Sg.Node{i, k, False{}, True{}, True{}} <> Sg.sweep(post)) : List<&2, Sg.Node>}

# LAW: a session never shows twice: no name is listed both as a storage
# and as a legacy file
law list_one_location:
  for +es: List<&2, Sg.Ent>
  for +n: Nat
  {Bool.and(Sg.mem(n, Sg.durables(es)), Sg.mem(n, Sg.legacies(es, es))) == False{} : Bool}

# LAW: after the import of the legacy file with stem s, s is listed as a
# storage (and so, by list_one_location, no more as a legacy file)
law list_import_lists_storage:
  for +es: List<&2, Sg.Ent>
  for +s: Nat
  {Sg.mem(s, Sg.durables(Sg.imported(s, es))) == True{} : Bool}

# LAW: an import changes the listing of no other name
law list_import_keeps_others:
  for +es: List<&2, Sg.Ent>
  for +s: Nat
  for +n: Nat
  for ne: {Nat.is_eq(s, n) == False{} : Bool}
  {Sg.mem(n, Sg.listing(Sg.imported(s, es))) == Sg.mem(n, Sg.listing(es)) : Bool}

# ---- recover ----

# LAWS (H4.8): a stuck model gets a recovery. Each law is an open claim
# about the model in bend/run.bend; PROOF.bend proves them (as Laws.<law>)
# with the lemmas of PROOF.bend section recover.

# (H4.8) A stuck model gets a recovery, each with a cap
# -----------------------------------------------------
# docs/harness.md H4.8, the recoveries of bend/run.bend (Rec): a length
# stop while the model still reasons, tool calls leaked as text, the same
# tool calls with the same results round after round. Every reply is
# free, in any order. A Redo is a noted error, so its retry ends its
# request with a new note (H4.7); the laws of H4 hold for every reply, so
# they hold for the reply a recovery makes. A recovery does not depend on
# the retry policy: a note is a new request, not a transient error.

# LAW: a length stop with no answer under the cap (fewer than `long`
# length notes in a row) is retried with the next length note
law rec_length_retries_with_a_note:
  for +rc: Rn.RCfg
  for +k: Rn.Rk
  for +row: Nat
  for +same: Nat
  for +last: Nat
  for under: {Rn.below(Rn.Rk.longs(k, row), Rn.RCfg.long(rc)) == True{} : Bool}
  {Rn.Rec.step(rc, Rn.Long{}, Rn.Rec{k, row, same, last}) == Rn.Dec{Rn.Redo{}, Rn.Rec{Rn.Longs{}, 1n+Rn.Rk.longs(k, row), same, last}} : Rn.Dec}

# LAW: after `long` length notes in a row, a length stop fails the run
law rec_length_gives_up:
  for +rc: Rn.RCfg
  for +k: Rn.Rk
  for +row: Nat
  for +same: Nat
  for +last: Nat
  for over: {Rn.below(Rn.Rk.longs(k, row), Rn.RCfg.long(rc)) == False{} : Bool}
  {Rn.Dec.act(Rn.Rec.step(rc, Rn.Long{}, Rn.Rec{k, row, same, last})) == Rn.Quit{} : Rn.Act}

# LAW: leaked calls that every parse and name an offered tool are rebuilt:
# the run reads them as the same calls made as tool calls
law rec_leak_rebuilt_is_calls:
  for +rc: Rn.RCfg
  for +h: Nat
  for kept: Bool
  for r: Rn.Rec
  {Rn.Rec.step(rc, Rn.Leak{True{}, h, kept}, r) == Rn.Rec.step(rc, Rn.Ran{h, kept}, r) : Rn.Dec}

# LAW: leaked calls that were not rebuilt, under the cap, are retried with
# the next leak note
law rec_leak_retries_with_a_note:
  for +rc: Rn.RCfg
  for +h: Nat
  for kept: Bool
  for +k: Rn.Rk
  for +row: Nat
  for +same: Nat
  for +last: Nat
  for under: {Rn.below(Rn.Rk.leaks(k, row), Rn.RCfg.leak(rc)) == True{} : Bool}
  {Rn.Rec.step(rc, Rn.Leak{False{}, h, kept}, Rn.Rec{k, row, same, last}) == Rn.Dec{Rn.Redo{}, Rn.Rec{Rn.Leaks{}, 1n+Rn.Rk.leaks(k, row), same, last}} : Rn.Dec}

# LAW: after `leak` leak notes in a row, the reply answers as text
law rec_leak_stands:
  for +rc: Rn.RCfg
  for +h: Nat
  for kept: Bool
  for +k: Rn.Rk
  for +row: Nat
  for +same: Nat
  for +last: Nat
  for over: {Rn.below(Rn.Rk.leaks(k, row), Rn.RCfg.leak(rc)) == False{} : Bool}
  {Rn.Dec.act(Rn.Rec.step(rc, Rn.Leak{False{}, h, kept}, Rn.Rec{k, row, same, last})) == Rn.Stand{} : Rn.Act}

# LAW: tool calls that make fewer than `repeat` rounds in a row run: the
# recoveries never stop a call that is not a repeat. The rounds in a row
# grow when the results are those of the last round; when the results
# change (a poll of a job that makes progress), a new row of 1 starts
law rec_calls_run:
  for +rc: Rn.RCfg
  for +h: Nat
  for +kept: Bool
  for +k: Rn.Rk
  for +row: Nat
  for +same: Nat
  for +last: Nat
  for fresh: {Rn.below(Rn.again(same, last, h), Rn.RCfg.repeat(rc)) == True{} : Bool}
  {Rn.Rec.step(rc, Rn.Ran{h, kept}, Rn.Rec{k, row, same, last}) == Rn.Dec{Rn.Exec{}, Rn.Rec{Rn.Free{}, 0n, Rn.ran.same(kept, Rn.again(same, last, h)), h}} : Rn.Dec}

# LAW: tool calls that would make `repeat` rounds in a row with the same
# results never run
law rec_repeat_never_runs:
  for +rc: Rn.RCfg
  for +h: Nat
  for kept: Bool
  for +k: Rn.Rk
  for +row: Nat
  for +same: Nat
  for +last: Nat
  for rep: {Rn.below(Rn.again(same, last, h), Rn.RCfg.repeat(rc)) == False{} : Bool}
  {Rn.Act.runs(Rn.Dec.act(Rn.Rec.step(rc, Rn.Ran{h, kept}, Rn.Rec{k, row, same, last}))) == False{} : Bool}

# LAW: such a repeat, under the cap, is retried with the next redirect
# note
law rec_repeat_redirects:
  for +rc: Rn.RCfg
  for +h: Nat
  for kept: Bool
  for +k: Rn.Rk
  for +row: Nat
  for +same: Nat
  for +last: Nat
  for rep: {Rn.below(Rn.again(same, last, h), Rn.RCfg.repeat(rc)) == False{} : Bool}
  for under: {Rn.below(Rn.Rk.loops(k, row), Rn.RCfg.redirect(rc)) == True{} : Bool}
  {Rn.Rec.step(rc, Rn.Ran{h, kept}, Rn.Rec{k, row, same, last}) == Rn.Dec{Rn.Redo{}, Rn.Rec{Rn.Loops{}, 1n+Rn.Rk.loops(k, row), same, last}} : Rn.Dec}

# LAW: after `redirect` redirect notes in a row, a repeat fails the run
law rec_repeat_gives_up:
  for +rc: Rn.RCfg
  for +h: Nat
  for kept: Bool
  for +k: Rn.Rk
  for +row: Nat
  for +same: Nat
  for +last: Nat
  for rep: {Rn.below(Rn.again(same, last, h), Rn.RCfg.repeat(rc)) == False{} : Bool}
  for over: {Rn.below(Rn.Rk.loops(k, row), Rn.RCfg.redirect(rc)) == False{} : Bool}
  {Rn.Dec.act(Rn.Rec.step(rc, Rn.Ran{h, kept}, Rn.Rec{k, row, same, last})) == Rn.Quit{} : Rn.Act}

# LAW: a user message ends the row: after it, no call is a repeat of a
# call before it
law rec_user_breaks_the_row:
  for +rc: Rn.RCfg
  for +k: Rn.Rk
  for +row: Nat
  for same: Nat
  for +last: Nat
  {Rn.Dec.r(Rn.Rec.step(rc, Rn.Said{}, Rn.Rec{k, row, same, last})) == Rn.Rec{k, row, 0n, last} : Rn.Rec}

# LAW: after any replies, the notes of a recovery in a row are at most
# its cap: every recovery stops at its cap
law rec_notes_capped:
  for +rc: Rn.RCfg
  for +os: List<&2, Rn.Out>
  {Rn.Rec.capped(rc, Rn.Rec.run(rc, os)) == True{} : Bool}

# LAW: after any replies, the run has not run the same calls with the
# same results max(repeat, 1) rounds in a row. This replaces the loop
# guard of H4.3 (a run failed after LOOP_ROUNDS = 6 such rounds): it is
# stronger, as no such row ever reaches `repeat` (5) rounds
law rec_never_runs_a_repeat:
  for +rc: Rn.RCfg
  for +os: List<&2, Rn.Out>
  {Rn.below(Rn.Rec.same(Rn.Rec.run(rc, os)), Nat.max(Rn.RCfg.repeat(rc), 1n)) == True{} : Bool}

# LAW: the harness never just watches a stuck model: a stuck reply (a
# length stop with no answer, leaked tool calls, tool calls) always gets
# an act that does something: its calls run (no repeat), a retry with a
# note, an answer, or the end of the run. It is never passed on as it is
law rec_stuck_gets_help:
  for +rc: Rn.RCfg
  for o: Rn.Out
  for r: Rn.Rec
  {Bool.or(Bool.not(Rn.Out.stuck(o)), Rn.Act.helps(Rn.Dec.act(Rn.Rec.step(rc, o, r)))) == True{} : Bool}

# LAW: a recovery's retry is a noted error, so its request ends with the
# note of the next attempt (run_cut_names_the_request): it never sends
# the request again (run_retry_sends_a_new_request)
law rec_redo_is_noted:
  for -pass: Rn.Reply
  {Rn.Act.reply(Rn.Redo{}, pass) == Rn.Error{False{}, True{}} : Rn.Reply}

# LAW: a recovery at its cap fails the run on the model, at once
law rec_quit_fails:
  for +cfg: Rn.Cfg
  for -pass: Rn.Reply
  for +r: Nat
  for +c: Nat
  for +a: Nat
  for +n: Nat
  for +p: Nat
  {Rn.call(cfg, Rn.Act.reply(Rn.Quit{}, pass), r, c, a, n, p) == Rn.St{Rn.Failed{Rn.Model{}}, r, c, a, n, p} : Rn.St}

# ---- catalog_union ----

# LAWS (C1): the built-in model catalog is one list, the union of the
# bundled snapshot and the compiled catalog. No source hides a model the
# other has; a model in both takes each field from one stated source; the
# result does not depend on the order the sources are read. Each law is
# an open claim about the model in bend/catalog_union.bend; PROOF.bend
# proves them (as Laws.<law>) with the lemmas of
# PROOF.bend section catalog_union.

# (C1) The catalog union
# ----------------------
# crates/eukhe-models/src/effective.rs `effective_catalog`, served by
# chain.rs `ModelCatalog::models`. bs is the bundled snapshot (pinned),
# cs the compiled catalog, k a model's key (its provider and id). Every
# input is free: any entries, any order.

# LAW: no source hides a model: the built-in catalog has a model exactly
# when the bundle or the compiled catalog has it
law union_hides_nothing:
  for +bs: List<&2, CU.Ent>
  for +cs: List<&2, CU.Ent>
  for +k: Nat
  {CU.has(CU.union(bs, cs), k) == Bool.or(CU.has(bs, k), CU.has(cs, k)) : Bool}

# LAW: one model list: when each source lists a model at most once, so
# does the built-in catalog
law union_lists_each_model_once:
  for +bs: List<&2, CU.Ent>
  for +cs: List<&2, CU.Ent>
  for +k: Nat
  for ub: {Nat.is_le(CU.count(bs, k), 1n) == True{} : Bool}
  for uc: {Nat.is_le(CU.count(cs, k), 1n) == True{} : Bool}
  {Nat.is_le(CU.count(CU.union(bs, cs), k), 1n) == True{} : Bool}

# LAW: a model that only the bundle has is the bundled entry
law union_bundled_only:
  for +bs: List<&2, CU.Ent>
  for +cs: List<&2, CU.Ent>
  for +k: Nat
  for +b: CU.Ent
  for hb: {CU.find(bs, k) == Some{b} : Maybe<&2, CU.Ent>}
  for hc: {CU.find(cs, k) == None{} : Maybe<&2, CU.Ent>}
  {CU.find(CU.union(bs, cs), k) == Some{b} : Maybe<&2, CU.Ent>}

# LAW: a model that only the compiled catalog has is the compiled entry
law union_compiled_only:
  for +bs: List<&2, CU.Ent>
  for +cs: List<&2, CU.Ent>
  for +k: Nat
  for +c: CU.Ent
  for hb: {CU.find(bs, k) == None{} : Maybe<&2, CU.Ent>}
  for hc: {CU.find(cs, k) == Some{c} : Maybe<&2, CU.Ent>}
  {CU.find(CU.union(bs, cs), k) == Some{c} : Maybe<&2, CU.Ent>}

# LAW: a model in both sources takes its api and its data from the
# bundled entry, and the optional field too when the bundled entry
# states it
law union_both_keeps_bundled:
  for +bs: List<&2, CU.Ent>
  for +cs: List<&2, CU.Ent>
  for +k: Nat
  for +b: CU.Ent
  for +c: CU.Ent
  for +v: Nat
  for hb: {CU.find(bs, k) == Some{b} : Maybe<&2, CU.Ent>}
  for hc: {CU.find(cs, k) == Some{c} : Maybe<&2, CU.Ent>}
  for hv: {CU.Ent.opt(b) == Some{v} : Maybe<&2, Nat>}
  {CU.find(CU.union(bs, cs), k) == Some{CU.Ent{CU.Ent.key(b), CU.Ent.api(b), CU.Ent.data(b), Some{v}}} : Maybe<&2, CU.Ent>}

# LAW: an optional field that the bundled entry leaves out comes from the
# compiled entry when both use the same api
law union_both_fills_from_compiled:
  for +bs: List<&2, CU.Ent>
  for +cs: List<&2, CU.Ent>
  for +k: Nat
  for +b: CU.Ent
  for +c: CU.Ent
  for hb: {CU.find(bs, k) == Some{b} : Maybe<&2, CU.Ent>}
  for hc: {CU.find(cs, k) == Some{c} : Maybe<&2, CU.Ent>}
  for hn: {CU.Ent.opt(b) == None{} : Maybe<&2, Nat>}
  for ha: {Nat.is_eq(CU.Ent.api(b), CU.Ent.api(c)) == True{} : Bool}
  {CU.find(CU.union(bs, cs), k) == Some{CU.Ent{CU.Ent.key(b), CU.Ent.api(b), CU.Ent.data(b), CU.Ent.opt(c)}} : Maybe<&2, CU.Ent>}

# LAW: and stays out when they use different apis
law union_both_other_api:
  for +bs: List<&2, CU.Ent>
  for +cs: List<&2, CU.Ent>
  for +k: Nat
  for +b: CU.Ent
  for +c: CU.Ent
  for hb: {CU.find(bs, k) == Some{b} : Maybe<&2, CU.Ent>}
  for hc: {CU.find(cs, k) == Some{c} : Maybe<&2, CU.Ent>}
  for hn: {CU.Ent.opt(b) == None{} : Maybe<&2, Nat>}
  for ha: {Nat.is_eq(CU.Ent.api(b), CU.Ent.api(c)) == False{} : Bool}
  {CU.find(CU.union(bs, cs), k) == Some{CU.Ent{CU.Ent.key(b), CU.Ent.api(b), CU.Ent.data(b), None{}}} : Maybe<&2, CU.Ent>}

# LAW: the result does not depend on the order the sources are read: the
# bundle first or the compiled catalog first, each source with its
# entries in any order (any two lists that agree at k), the model with
# key k comes out the same
law union_order_free:
  for +k: Nat
  for +xs: List<&2, CU.Ent>
  for +xs2: List<&2, CU.Ent>
  for +ys: List<&2, CU.Ent>
  for +ys2: List<&2, CU.Ent>
  for sx: {CU.find(xs, k) == CU.find(xs2, k) : Maybe<&2, CU.Ent>}
  for sy: {CU.find(ys, k) == CU.find(ys2, k) : Maybe<&2, CU.Ent>}
  {CU.find(CU.read(CU.Cat{CU.Bundled{}, xs}, CU.Cat{CU.Compiled{}, ys}), k) == CU.find(CU.read(CU.Cat{CU.Compiled{}, ys2}, CU.Cat{CU.Bundled{}, xs2}), k) : Maybe<&2, CU.Ent>}

# ---- cron ----

# LAWS (D2): the cron store shared by processes. Each law is an open claim
# about the model in bend/cron.bend; PROOF.bend proves them (as
# Laws.<law>) with the lemmas of PROOF.bend section cron.

# (D2) Cron
# ---------
# docs/state.md D2. The cron jobs file `cron-jobs.json` (bend/cron.bend),
# shared by any number of processes. Every input is free: any events of
# any processes in any order (make a job, claim the due jobs, recover
# claims, finish a run good, failed or skipped, unwind a pass, die), any
# user actions (cancel, resume), any time, any records this build cannot
# read, a corrupt file at any point.

# LAW: after any events, each job is run by at most one process, and that
# run holds the claim on record; no occurrence of a job starts twice (the
# occurrences that started fall strictly, the newest first); a one-shot
# starts at most once
law cron_fires_once:
  for +evs: List<&2, Cr.Ev>
  Cr.FiresAll(Cr.S.recs(Cr.run(evs)))

# LAW: after any events, a finished one-shot has no run: it is finished
# only after its run ended
law cron_once_finished_after_end:
  for +evs: List<&2, Cr.Ev>
  Cr.EndsAll(Cr.S.recs(Cr.run(evs)))

# LAW: from any file (records read or not, corrupt or not), a step that
# is not the file's corruption keeps every record: each job record this
# build cannot read with the same bytes, each job, each claim record this
# build cannot read, the corrupt file (in place or moved aside, never
# written over), each file moved aside
law cron_never_drops:
  for +s: Cr.S
  for +e: Cr.Ev
  for +t: Nat
  for +i: Nat
  {Cr.Ev.is_corrupt(e) == False{} : Bool} -> Cr.Keeps(t, i, s, Cr.step(s, e))

# LAW: from any state, a step of process p removes the claim of process o
# on job i only when o is p or o is dead; no other step (but the file's
# corruption) removes a claim
law cron_claim_owned:
  for +s: Cr.S
  for +e: Cr.Ev
  for +i: Nat
  for +x: Nat
  for +o: Nat
  {Cr.Ev.is_corrupt(e) == False{} : Bool} -> {Cr.claim_of(i, Cr.S.recs(s)) == Some{Cr.Claim{x, o}} : Maybe<&2, Cr.Claim>} -> Or({Cr.claim_of(i, Cr.S.recs(Cr.step(s, e))) == Some{Cr.Claim{x, o}} : Maybe<&2, Cr.Claim>}, Or({Cr.Ev.by(e) == Some{o} : Maybe<&2, Nat>}, {Cr.has(o, Cr.S.dead(s)) == True{} : Bool}))

# LAW: after any events, a job counted at most CAP failed runs in a row,
# and an active job fewer: so the CAP-th failure in a row stops it; a
# stopped (paused) job stays stopped through every step that is not a user
# action; the pause after the k-th failure is never shorter than after the
# (k-1)-th, and a failure never moves the next run before its pause ends
law cron_backoff_bounded:
  for +evs: List<&2, Cr.Ev>
  for +s: Cr.S
  for +e: Cr.Ev
  for +i: Nat
  for +k: Nat
  for +c: Nat
  for +nx: Maybe<&2, Nat>
  (Cr.StopsAll(Cr.S.recs(Cr.run(evs))) & (({Cr.Ev.is_user(e) == False{} : Bool} -> Cr.StaysPaused(i, s, Cr.step(s, e))) & ({Nat.is_le(Cr.delay(k), Cr.delay(1n+k)) == True{} : Bool} & {Nat.is_le(Nat.add(c, Cr.delay(k)), Cr.later(nx, Nat.add(c, Cr.delay(k)))) == True{} : Bool})))

# ---- supervisor ----

# (D1) Supervisor
# ---------------
# docs/daemon.md D1: the supervisor, its workers, a lost supervisor, a
# daemon replacement, the attaches after a restart. The models are
# bend/supervise.bend (the restart budget and the timeouts),
# bend/revive.bend (busy evidence), bend/orphan.bend (a lost supervisor's
# worker), bend/launcher.bend (the idle shutdown and adoption),
# bend/replace.bend (the launcher's replacement verdict) and
# bend/notice.bend (the kernel restore notices a view shows); the bridge
# tests crates/eukhe-daemon/src/supervision_bridge.rs,
# crates/eukhe-tui/src/daemon_build/bridge.rs and
# crates/eukhe-tui/src/restore_notices.rs run the Rust code and each
# model on the same scenarios. Every input is free: any configuration, any
# gaps between failures, any run length, any events and operations in any
# order, any builds.

# LAW: a crash loop is given up. After any earlier failures, a failure
# followed by k more failures, all inside the window, gives the worker up
law restart_gives_up:
  for +c: Su.Cfg
  for +pre: List<&2, Nat>
  for +g: Nat
  for +gs: List<&2, Nat>
  for many: {List.length(&2, Nat, gs) == Su.Cfg.k(c) : Nat}
  for fast: {Nat.is_lt(Su.span(gs), Su.Cfg.w(c)) == True{} : Bool}
  {Su.gives_up(Su.verdict(c, Su.failures(c, List.append(&2, Nat, pre, g <> gs)))) == True{} : Bool}

# LAW: every timeout comes after the timeouts it waits for (Su.Tm.ordered
# lists them), whatever the base values
law timeouts_ordered:
  for +t: Su.Tm
  {Su.Tm.ordered(t) == True{} : Bool}

# LAW: a run of any length revives: a boot within the boot window b after
# the crash finds its busy evidence fresh, with a refresh every h > 0 ms
# and the max age h + b
law revive_after_refresh:
  for +h: Nat
  for pos: {Nat.is_lt(0n, h) == True{} : Bool}
  for +b: Nat
  for +c: Nat
  for +d: Nat
  for soon: {Nat.is_le(d, b) == True{} : Bool}
  {Rv.fresh(Nat.add(h, b), Rv.age(h, c, d)) == True{} : Bool}

# LAW: a lost supervisor's worker never aborts work a later supervisor can
# resume: its exit aborts nothing and records the session busy exactly
# when it held work
law orphan_never_aborts_resumable:
  for +window: Nat
  for +evs: List<&2, Or.Ev>
  Or.Sound(Or.run(window, evs))

# LAW: an idle shutdown never aborts a run, in any order of prompts, run
# ends, quiesces, releases and commits on any workers
law idle_shutdown_never_aborts:
  for +bs: List<&2, Bool>
  for +ops: List<&2, La.Op>
  {La.St.aborted(La.run(bs, ops)) == 0n : Nat}

# LAW: a supervisor adopts a worker only when the worker reports the
# supervisor's build
law adopt_same_build:
  for +sup: Nat
  for +w: Maybe<&2, Nat>
  for adopted: {La.adoption(sup, w) == La.Adopt{} : La.Adoption}
  {w == Some{sup} : Maybe<&2, Nat>}

# LAW: client starts never take the daemon back to a lower build. For any
# client starts (any builds, interactive or background), no daemon ranks
# below a daemon that ran before it
law replace_never_downgrades:
  for +ss: List<&2, Rp.Start>
  {Rp.never_back(Rp.daemons(ss)) == True{} : Bool}

# LAW: replacements stop. Client starts whose builds are all in bs (k
# builds) replace the daemon k - 1 times at most
law replacement_terminates:
  for +bs: List<&2, Rp.Build>
  for +ss: List<&2, Rp.Start>
  for cover: {Rp.covers(bs, ss) == True{} : Bool}
  {Nat.is_le(Rp.replaced(ss), Nat.sub(List.length(&2, Rp.Build, bs), 1n)) == True{} : Bool}

# LAW: a background client (the dashboard, the gateway, ACP, a reconnect)
# never replaces a running daemon
law background_never_replaces:
  for +c: Rp.Build
  for +d: Rp.Build
  {Rp.after(Rp.Start{c, Rp.Background{}}, Some{d}) == d : Rp.Build}

# LAW: an attach never shows a kernel restore notice again. After any
# restores, live notices and attaches (reconnects, worker restarts), in
# any order, each stored notice showed at most once (bend/notice.bend;
# the bridge is crates/eukhe-tui/src/restore_notices.rs)
law notice_shown_once:
  for +evs: List<&2, No.Ev>
  {No.once(No.run(evs)) == True{} : Bool}

# LAW: restore notices do not accumulate. After any events and one more
# attach, the restore rows the view showed equal the restores
law notice_per_restore:
  for +evs: List<&2, No.Ev>
  {No.total(No.run(List.append(&2, No.Ev, evs, [No.Reconnect{}]))) == No.restores(evs) : Nat}

# ---- gateway_width ----

# LAWS: the Signal gateway aligns a table by display width. Each law is an
# open claim about the model in bend/gateway_width.bend (the formatter
# `push_table` of crates/eukhe-gateway/src/style.rs); PROOF.bend proves
# them (as Laws.<law>) with the lemmas of
# PROOF.bend section gateway_width.

# LAW: every row of a formatted table has the same display width per
# column: each row of the table (pre, row, post) renders as the widths of
# the columns, then its own last cell (the last column is not padded)
law table_aligned:
  for +pre: List<&2, List<&2, List<&2, Nat>>>
  for +row: List<&2, List<&2, Nat>>
  for +post: List<&2, List<&2, List<&2, Nat>>>
  {Gw.line(Nat.sub(Gw.cols(List.append(&2, List<&2, List<&2, Nat>>, pre, row <> post)), 1n), Gw.Display{}, List.append(&2, List<&2, List<&2, Nat>>, pre, row <> post), row, 0n) == List.append(&2, Nat, Gw.widths(Nat.sub(Gw.cols(List.append(&2, List<&2, List<&2, Nat>>, pre, row <> post)), 1n), Gw.Display{}, List.append(&2, List<&2, List<&2, Nat>>, pre, row <> post), 0n), [Gw.get.w(row, Gw.Display{}, Nat.sub(Gw.cols(List.append(&2, List<&2, List<&2, Nat>>, pre, row <> post)), 1n))]) : List<&2, Nat>}

# LAW: an ASCII table (every glyph 1 wide) renders as the old formatter
# rendered it, which counted the characters of a cell
law ascii_unchanged:
  for +rows: List<&2, List<&2, List<&2, Nat>>>
  for +ones: Gw.Ones.rows(rows)
  {Gw.table(Gw.Display{}, rows) == Gw.table(Gw.Chars{}, rows) : List<&2, List<&2, Nat>>}

# ---- tui_color ----

# LAWS (T3): terminal colors. Each law is an open claim about the model
# in bend/tui_color.bend (with the theme tables of bend/theme.bend);
# PROOF.bend proves them (as Laws.<law>) with the lemmas of
# PROOF.bend section tui_color.

# (T3) Terminal colors
# --------------------
# docs/interface.md "Terminal colors", the model in bend/tui_color.bend:
# the effort ramp, the usage bands and the color roles of
# crates/eukhe-tui. Every input is free: any ramp ends and any ladder
# length, any token count and any window. The bridge test
# crates/eukhe-tui/src/theme/bridge.rs checks that the Rust ramp, the Rust
# bands and the Rust roles equal the model.

# LAW: the effort ramp has one rung for each level the model offers
law tui_effort_ramp_length:
  for lo: TC.Px
  for hi: TC.Px
  for n: Nat
  {List.length(&2, TC.Px, TC.ramp(lo, hi, n)) == n : Nat}

# LAW: for any ladder length, along the effort ramp every channel moves
# from the low end toward the high end, never back
law tui_effort_ramp_ordered:
  for lo: TC.Px
  for hi: TC.Px
  for n: Nat
  {TC.ordered(lo, hi, TC.ramp(lo, hi, n)) == True{} : Bool}

# LAW: for any ladder length up to the widest channel distance of the
# ends, no two rungs of the effort ramp have the same color
law tui_effort_ramp_distinct:
  for lo: TC.Px
  for hi: TC.Px
  for n: Nat
  for fits: {Nat.is_le(n, TC.span(lo, hi)) == True{} : Bool}
  {TC.distinct(TC.ramp(lo, hi, n)) == True{} : Bool}

# LAW: in every shipped theme, no two rungs of the effort ramp have the
# same color, for any ladder of the level vocabulary
law tui_effort_shipped_distinct:
  for s: T.Shipped
  for n: Nat
  for fits: {Nat.is_le(n, TC.ladder.max()) == True{} : Bool}
  {TC.distinct(TC.ramp(TC.shipped.lo(s), TC.shipped.hi(s), n)) == True{} : Bool}

# LAW: every usage band is a fraction of the window above zero and at
# most one, and each band is above the band before it
law tui_usage_bands_ascend:
  {TC.ascend(TC.bands()) == True{} : Bool}

# LAW: more tokens in the same window never give a lower usage band
law tui_usage_band_monotone:
  for t: Nat
  for e: Nat
  for w: Nat
  {Nat.is_le(TC.band(t, w), TC.band(Nat.add(t, e), w)) == True{} : Bool}

# LAW: the usage band depends only on the fraction of the window in use:
# the same fraction of a window k times as large gives the same band
law tui_usage_band_fraction:
  for k: Nat
  for t: Nat
  for w: Nat
  {TC.band(Nat.mul(1n+k, t), Nat.mul(1n+k, w)) == TC.band(t, w) : Nat}

# LAW: every color role of the terminal UI resolves in the palette of
# every valid theme file
law tui_roles_resolve:
  for f: T.Th
  for v: {T.valid(f) == True{} : Bool}
  {TC.resolves(T.palette(f), TC.roles()) == True{} : Bool}

# LAW: every color role of the terminal UI paints a color in every
# shipped theme
law tui_roles_shipped:
  for s: T.Shipped
  {TC.paints(T.table(s), TC.roles()) == True{} : Bool}

# ---- fsmode ----

# LAWS (G1, file modes, the socket dir and the working dir): who
# reaches eukhe's own state. Each law is an open claim about the model in
# bend/fsmode.bend; PROOF.bend proves them (as Laws.<law>) with the lemmas
# of PROOF.bend section fsmode.

# (G1) Path policy
# ----------------

# File modes, the socket dir and the working dir
# ----------------------------------------------
# docs/runtime.md "Local access", the model in bend/fsmode.bend; the Rust
# bridge test crates/eukhe-daemon/src/fsmode_bridge.rs runs the real
# socket-dir check, the peer rule, the real creation paths and the real
# session cwd check against bend/bridge_fsmode.bend.

# LAW: the daemon binds in a socket dir only when the dir is a real
# directory (not a link), this uid owns it, and no group or other user
# may write in it
law socket_dir_owned:
  for d: Fs.Seen
  for used: {Fs.socket_dir(d) == Fs.Use{} : Fs.Verdict}
  {Fs.Seen.safe(d) == True{} : Bool}

# LAW: a safe socket dir is used (the check refuses nothing it must not)
law socket_dir_progress:
  for d: Fs.Seen
  for safe: {Fs.Seen.safe(d) == True{} : Bool}
  {Fs.socket_dir(d) == Fs.Use{} : Fs.Verdict}

# LAW: a missing socket dir is created with mode 0700
law socket_dir_created:
  for mine: Bool
  for loose: Bool
  {Fs.socket_dir(Fs.Seen{Fs.Missing{}, mine, loose}) == Fs.Create{Fs.dir_mode()} : Fs.Verdict}

# LAW: the dir the daemon creates with mode 0700 is then used
law socket_dir_created_used:
  {Fs.socket_dir(Fs.made(Fs.dir_mode())) == Fs.Use{} : Fs.Verdict}

# LAW: a socket peer is accepted only when its uid is this process's uid
law peer_same_uid:
  for p: Nat
  for own: Nat
  for ok: {Fs.peer(p, own) == Fs.Accept{} : Fs.Peer}
  {p == own : Nat}

# LAW: a peer of this process's uid is accepted
law peer_own_accepted:
  for own: Nat
  {Fs.peer(own, own) == Fs.Accept{} : Fs.Peer}

# LAW: every file and dir eukhe creates under its home has no group or
# other permission bit
law private_on_create:
  for k: Fs.Made
  {Fs.Mode.loose(Fs.made_mode(k)) == False{} : Bool}

# LAW: an accepted session create runs in the dir it named, and that dir
# exists
law cwd_is_explicit:
  for c: Fs.Cwd
  for p: Nat
  for ok: {Fs.open(c) == Fs.Opened{p} : Fs.Open}
  {c == Fs.DirCwd{p} : Fs.Cwd}

# LAW: a create that names no working dir is refused
law cwd_none_refused:
  {Fs.open(Fs.NoCwd{}) == Fs.NeedsCwd{} : Fs.Open}

# LAW: a create whose working dir is gone is refused, and the refusal
# names that dir
law cwd_gone_refused:
  for p: Nat
  {Fs.open(Fs.GoneCwd{p}) == Fs.Gone{p} : Fs.Open}

# LAW: a create whose working dir is a file is refused, and the refusal
# names that path
law cwd_file_refused:
  for p: Nat
  {Fs.open(Fs.FileCwd{p}) == Fs.NotDir{p} : Fs.Open}

# LAW: a create that names an existing dir runs in it
law cwd_dir_opens:
  for p: Nat
  {Fs.open(Fs.DirCwd{p}) == Fs.Opened{p} : Fs.Open}

# ---- path_policy ----

# LAWS (G1): the path policy. Each law is an open claim about the model
# in bend/path_policy.bend; PROOF.bend proves them (as Laws.<law>) with the
# lemmas of PROOF.bend section path_policy.

# (G1) Path policy
# ----------------
# docs/tools.md S7: one policy for the `bash` tool and the document
# tools (crates/eukhe-types/src/path_policy.rs). A path is a list of
# segments from `/`; the symlinks are free (any location, any target,
# from `/` or from the link's directory, loops included); the policy is
# free (any roots, protected rules and secret entries). An access is
# judged on the real path; its effects run unasked only when the auto
# set (`shell.autoEffects`, any value) allows each of them. The user's
# answer is free: yes, no, or none (no client answered).

# LAW: a path is judged by its real path: unless its links looped, no
# prefix of the path a resolution reaches is a symlink (each link it met
# was replaced by its target)
law path_real_has_no_link:
  for +ls: List<&2, Pp.Link>
  for +segs: List<&2, Tl.Seg>
  {Bool.or(Pp.Res.looped(Pp.real(ls, segs)), Pp.linkfree(ls, Pp.Res.at(Pp.real(ls, segs)))) == True{} : Bool}

# LAW: a path whose real path is under a secret entry is Secret, whatever
# else covers it
law path_secret_wins:
  for +pol: Pp.Pol
  for +ls: List<&2, Pp.Link>
  for +segs: List<&2, Tl.Seg>
  for hit: {Pp.any_under(Pp.Pol.secret(pol), Pp.Res.at(Pp.real(ls, segs))) == True{} : Bool}
  {Pp.class(pol, ls, segs) == Pp.Secret{} : Pp.Cls}

# LAW: a path is Inside only when its links did not loop, no secret
# covers its real path, no rule protects it, it is no ancestor of a
# protected or secret entry, and a workspace root holds it
law path_inside_is_safe:
  for +pol: Pp.Pol
  for +ls: List<&2, Pp.Link>
  for +segs: List<&2, Tl.Seg>
  for inside: {Pp.class(pol, ls, segs) == Pp.Inside{} : Pp.Cls}
  {Pp.safe(pol, Pp.real(ls, segs)) == True{} : Bool}

# LAW: an ancestor of a protected or secret entry (a move or a removal of
# it moves or removes the entry) is Protected or Secret
law path_ancestor_guarded:
  for +pol: Pp.Pol
  for +ls: List<&2, Pp.Link>
  for +segs: List<&2, Tl.Seg>
  for anc: {Pp.any_ancestor(List.append(&2, List<&2, Nat>, Pp.entries(Pp.Pol.rules(pol)), Pp.Pol.secret(pol)), Pp.Res.at(Pp.real(ls, segs))) == True{} : Bool}
  {Pp.Cls.guarded(Pp.class(pol, ls, segs)) == True{} : Bool}

# LAW: a write runs without the user's yes only Inside the workspace:
# never Outside, never to eukhe's config or credentials, never to a
# secret, whatever the auto set holds
law gate_write_auto_only_inside:
  for c: Pp.Cls
  for +auto: List<&2, Nat>
  for ans: Pp.Ans
  for ran: {Pp.runs(c, Pp.Wr{}, auto, ans) == True{} : Bool}
  for no: {Pp.Ans.yes(ans) == False{} : Bool}
  {c == Pp.Inside{} : Pp.Cls}

# LAW: a read of a secret (a read or a list of one, a search of a
# directory that holds one) runs only on the user's yes, whatever the auto
# set holds
law gate_secret_read_needs_yes:
  for c: Pp.Cls
  for a: Pp.Acc
  for +auto: List<&2, Nat>
  for ans: Pp.Ans
  for s: {Pp.secret_read(c, a) == True{} : Bool}
  for ran: {Pp.runs(c, a, auto, ans) == True{} : Bool}
  {Pp.Ans.yes(ans) == True{} : Bool}

# LAW: the user's yes runs any access
law gate_yes_runs:
  for c: Pp.Cls
  for a: Pp.Acc
  for +auto: List<&2, Nat>
  {Pp.runs(c, a, auto, Pp.Yes{}) == True{} : Bool}

# LAW: with writes in the auto set, a write Inside runs without a
# question
law gate_inside_write_runs:
  for +auto: List<&2, Nat>
  for ans: Pp.Ans
  for w: {Tl.elem(auto, 1n) == True{} : Bool}
  {Pp.runs(Pp.Inside{}, Pp.Wr{}, auto, ans) == True{} : Bool}

# LAW: no sequence of agent writes through any paths, each judged by the
# gate on its real path and landing there, without a yes of the user,
# changes a guarded location: eukhe's config (where the auto set,
# ssh.hosts and mcpServers live) and the secrets stay as they were,
# whatever the auto set holds
law config_needs_yes:
  for es: List<&2, Pp.Put>
  for +pol: Pp.Pol
  for +ls: List<&2, Pp.Link>
  for +auto: List<&2, Nat>
  for +cs: List<&2, Pp.Cell>
  for no: {Pp.any_yes(es) == False{} : Bool}
  {Pp.guarded(Pp.run(es, pol, ls, auto, cs), pol) == Pp.guarded(cs, pol) : List<&2, Pp.Cell>}

# ---- child_env ----

# LAWS (G3): no credential reaches a child. Each law is an open claim
# about the model in bend/child_env.bend; PROOF.bend proves them (as
# Laws.<law>) with the lemmas of PROOF.bend section child_env.

# (G3) No credential reaches a child
# ----------------------------------
# The environment of a child the host starts for an agent: the overlay
# over the base, less the credential names (bend/child_env.bend). The
# `bash` tool's external steps get an empty keep list; a local kernel gets
# the names the user's own MCP config reads a credential from. Every input
# is free: any registry, any keep list, any base, any overlay (so no
# overlay can add a credential back).

# LAW: no variable of the environment of an external step of the `bash`
# tool has a credential name
law env_drops_credentials:
  for +reg: List<&2, String>
  for base: List<&2, Env.Var>
  for over: List<&2, Env.Var>
  for +v: Env.Var
  for i: Env.In(v, Env.child(reg, Nil{}, base, over))
  {Env.cred(reg, Env.Var.name(v)) == False{} : Bool}

# LAW: a variable of the environment of a kernel has a credential name
# only when the keep list holds that name and it is no provider name
law env_kernel_keeps_only_listed:
  for +reg: List<&2, String>
  for +keep: List<&2, String>
  for base: List<&2, Env.Var>
  for over: List<&2, Env.Var>
  for +v: Env.Var
  for i: Env.In(v, Env.child(reg, keep, base, over))
  for c: {Env.cred(reg, Env.Var.name(v)) == True{} : Bool}
  ({Env.listed(keep, Env.Var.name(v)) == True{} : Bool} & {Env.registered(reg, Env.Var.name(v)) == False{} : Bool})

# LAW: every variable of the overlay over the base whose name is not a
# credential reaches the child, with its value
law env_keeps_the_rest:
  for +reg: List<&2, String>
  for +keep: List<&2, String>
  for base: List<&2, Env.Var>
  for over: List<&2, Env.Var>
  for +v: Env.Var
  for i: Env.In(v, Env.merge(base, over))
  for c: {Env.cred(reg, Env.Var.name(v)) == False{} : Bool}
  Env.In(v, Env.child(reg, keep, base, over))

# LAW: every variable of the overlay over the base whose name the keep
# list holds, and that is no provider name, reaches the kernel, with its
# value
law env_keeps_listed:
  for +reg: List<&2, String>
  for +keep: List<&2, String>
  for base: List<&2, Env.Var>
  for over: List<&2, Env.Var>
  for +v: Env.Var
  for i: Env.In(v, Env.merge(base, over))
  for k: {Env.listed(keep, Env.Var.name(v)) == True{} : Bool}
  for r: {Env.registered(reg, Env.Var.name(v)) == False{} : Bool}
  Env.In(v, Env.child(reg, keep, base, over))

# The overlay over the base (every input free: duplicate names too)

# n is the name of a variable of xs
def env_named(+n: String, xs: List<&2, Env.Var>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case v <> rest:
      Bool.or(String.eq(Env.Var.name(v), n), env_named(n, rest))

# LAW: no variable reaches a child that the overlay over the base does
# not hold: the filter only drops, it never invents or changes a value
law env_child_from_merge:
  for +reg: List<&2, String>
  for +keep: List<&2, String>
  for +base: List<&2, Env.Var>
  for +over: List<&2, Env.Var>
  for +v: Env.Var
  for i: Env.In(v, Env.child(reg, keep, base, over))
  Env.In(v, Env.merge(base, over))

# LAW: every variable of the overlay is in the overlay over the base
law env_overlay_in_merge:
  for base: List<&2, Env.Var>
  for +over: List<&2, Env.Var>
  for +v: Env.Var
  for i: Env.In(v, over)
  Env.In(v, Env.merge(base, over))

# LAW: a variable of the base whose name the overlay does not name is in
# the overlay over the base
law env_base_in_merge:
  for +base: List<&2, Env.Var>
  for +over: List<&2, Env.Var>
  for +v: Env.Var
  for i: Env.In(v, base)
  for free: {env_named(Env.Var.name(v), over) == False{} : Bool}
  Env.In(v, Env.merge(base, over))

# LAW: a variable of the overlay over the base whose name the overlay
# names comes from the overlay: the overlay hides every variable of the
# base with that name
law env_merge_named_from_overlay:
  for +base: List<&2, Env.Var>
  for +over: List<&2, Env.Var>
  for +v: Env.Var
  for i: Env.In(v, Env.merge(base, over))
  for hit: {env_named(Env.Var.name(v), over) == True{} : Bool}
  Env.In(v, over)

# LAW: every variable of the overlay over the base comes from the
# overlay, or from the base under a name the overlay does not name
law env_merge_from_inputs:
  for +base: List<&2, Env.Var>
  for +over: List<&2, Env.Var>
  for +v: Env.Var
  for i: Env.In(v, Env.merge(base, over))
  Or(Env.In(v, over), (Env.In(v, base) & {env_named(Env.Var.name(v), over) == False{} : Bool}))

# The credential names (crates/eukhe-ai/src/env_api_keys.rs)

# LAW: anchor: a name whose ASCII upper case contains a secret pattern is
# a credential, at its start, middle or end, in any case: API_KEY, APIKEY,
# TOKEN, SECRET, PASSWORD, PASSWD, PASSPHRASE, CREDENTIAL, PRIVATE_KEY,
# ACCESS_KEY
law env_cred_example:
  {[Env.cred(Nil{}, "OPENAI_API_KEY"), Env.cred(Nil{}, "my_apikey"), Env.cred(Nil{}, "GITHUB_TOKEN"), Env.cred(Nil{}, "TOKENIZERS_PARALLELISM"), Env.cred(Nil{}, "AWS_WEB_IDENTITY_TOKEN_FILE"), Env.cred(Nil{}, "aws_secret_access_key"), Env.cred(Nil{}, "PGPASSWORD"), Env.cred(Nil{}, "db_passwd"), Env.cred(Nil{}, "GPG_PASSPHRASE"), Env.cred(Nil{}, "GOOGLE_APPLICATION_CREDENTIALS"), Env.cred(Nil{}, "TLS_PRIVATE_KEY"), Env.cred(Nil{}, "S3_ACCESS_KEY")] == [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}] : List<&2, Bool>}

# LAW: anchor: names a child needs are no credential: there is no KEY,
# AUTH or PASS pattern
law env_not_cred_example:
  {[Env.cred(Nil{}, "PATH"), Env.cred(Nil{}, "HOME"), Env.cred(Nil{}, "SSH_AUTH_SOCK"), Env.cred(Nil{}, "XAUTHORITY"), Env.cred(Nil{}, "KEYTIMEOUT"), Env.cred(Nil{}, "SSH_ASKPASS"), Env.cred(Nil{}, "LS_COLORS")] == [False{}, False{}, False{}, False{}, False{}, False{}, False{}] : List<&2, Bool>}

# LAW: anchor: a provider name is a credential and a provider name in any
# case, by the registry alone
law env_registry_example:
  {[Env.cred(["AWS_PROFILE"], "aws_profile"), Env.registered(["AWS_PROFILE"], "aws_profile"), Env.registered(Nil{}, "aws_profile"), Env.cred(Nil{}, "AWS_PROFILE")] == [True{}, True{}, False{}, False{}] : List<&2, Bool>}

# LAW: anchor (the Rust tests of child_env): an external step gets no
# credential of the base or the overlay, and the overlay wins
law env_step_example:
  {Env.child(["OPENAI_API_KEY"], Nil{}, [Env.Var{"PATH", "/bin"}, Env.Var{"OPENAI_API_KEY", "sk"}, Env.Var{"db_password", "h"}, Env.Var{"HOME", "/home"}], [Env.Var{"GITHUB_TOKEN", "g"}, Env.Var{"PATH", "/usr/bin"}, Env.Var{"EUKHE_CODING_AGENT_DIR", "/agent"}]) == [Env.Var{"PATH", "/usr/bin"}, Env.Var{"EUKHE_CODING_AGENT_DIR", "/agent"}, Env.Var{"HOME", "/home"}] : List<&2, Env.Var>}

# LAW: anchor: a kernel keeps only the kept credentials that are no
# provider name
law env_kernel_example:
  {Env.child(["OPENAI_API_KEY"], ["GITHUB_TOKEN", "OPENAI_API_KEY"], [Env.Var{"PATH", "/bin"}, Env.Var{"OPENAI_API_KEY", "sk"}, Env.Var{"GITHUB_TOKEN", "g"}, Env.Var{"SLACK_SECRET", "x"}], Nil{}) == [Env.Var{"PATH", "/bin"}, Env.Var{"GITHUB_TOKEN", "g"}] : List<&2, Env.Var>}

# ---- shell_classification ----

# shell_classification: the laws of section G2 (PROOF.bend proves them
# as Laws.<law>).

# (G2) Shell classification
# -------------------------
# docs/tools.md S7, the gate model of bend/tools.bend part 4. A step has a
# set of effects (codes: 0 read, 1 write, 2 exec, 3 net, 4 outside, 5
# protected, 6 secret): every effect of every part of it (its command,
# each redirection, each path it names; every command an external script
# holds). A part names a path that is or holds a secret, or not; only such
# a part gives the secret effect. Every input is free: any parts, any
# effects, any auto set (codes 4 to 6 in it too), any answers of the user.

# LAW: a step made of parts has every effect of every part
law step_holds_every_part:
  for +pre: List<&2, List<&2, Nat>>
  for +p: List<&2, Nat>
  for +post: List<&2, List<&2, Nat>>
  for +c: Nat
  for has: {Tl.elem(p, c) == True{} : Bool}
  {Tl.elem(Tl.join(List.append(&2, List<&2, Nat>, pre, p <> post)), c) == True{} : Bool}

# LAW: a step has the secret effect (6) only when one of its parts names
# a path that is or holds a secret (an operand, an option value, a
# redirection target, the working directory of a command that reads it
# because it names no path): a step whose parts name none has no secret
# effect, whatever else they hold
law secret_needs_a_secret_path:
  for +ps: List<&2, Tl.Part>
  for has: {Tl.elem(Tl.join(Tl.parts.effs(ps)), 6n) == True{} : Bool}
  {Tl.parts.secret(ps) == True{} : Bool}

# LAW: a part that names a path that is or holds a secret gives its step
# the secret effect (6)
law secret_path_gives_secret:
  for +pre: List<&2, Tl.Part>
  for +p: Tl.Part
  for +post: List<&2, Tl.Part>
  for named: {Tl.Part.secret(p) == True{} : Bool}
  {Tl.elem(Tl.join(Tl.parts.effs(List.append(&2, Tl.Part, pre, p <> post))), 6n) == True{} : Bool}

# LAW: a step with one effect that is not in the auto set, or that no auto
# set may hold, does not run without a question
law auto_needs_every_effect:
  for +s: Tl.Step
  for +auto: List<&2, Nat>
  for +c: Nat
  for has: {Tl.elem(Tl.Step.effs(s), c) == True{} : Bool}
  for out: {Bool.and(Tl.grantable(c), Tl.elem(auto, c)) == False{} : Bool}
  {Tl.auto.at(auto, s) == False{} : Bool}

# LAW: a write outside the workspace (4), a write to a protected place (5)
# and a read of a secret (6) never run without a question, whatever the
# auto set holds
law auto_never_sensitive:
  for +s: Tl.Step
  for +auto: List<&2, Nat>
  for +c: Nat
  for has: {Tl.elem(Tl.Step.effs(s), c) == True{} : Bool}
  for held: {Nat.is_le(4n, c) == True{} : Bool}
  {Tl.auto.at(auto, s) == False{} : Bool}

# LAW: a step made of parts runs without a question only when every effect
# of every part is within the auto set
law composed_needs_every_part:
  for +i: Nat
  for +pre: List<&2, List<&2, Nat>>
  for +p: List<&2, Nat>
  for +post: List<&2, List<&2, Nat>>
  for +auto: List<&2, Nat>
  for +c: Nat
  for has: {Tl.elem(p, c) == True{} : Bool}
  for out: {Bool.and(Tl.grantable(c), Tl.elem(auto, c)) == False{} : Bool}
  {Tl.auto.at(auto, Tl.Step{i, Tl.join(List.append(&2, List<&2, Nat>, pre, p <> post))}) == False{} : Bool}

# LAW: a step whose effects are within the auto set runs without a
# question: it uses no answer of the user
law auto_runs_within:
  for +s: Tl.Step
  for +post: List<&2, Tl.Step>
  for +auto: List<&2, Nat>
  for ans: List<&2, Bool>
  for w: {Tl.within(Tl.Step.effs(s), auto) == True{} : Bool}
  {Tl.exec(s <> post, auto, ans) == Tl.ran.add(s, Tl.exec(post, auto, ans)) : Tl.Ran}

# LAW: a step whose effects are not within the auto set runs only with
# the user's yes: with no answer it does not run, and the script stops
law held_needs_a_yes:
  for +s: Tl.Step
  for +post: List<&2, Tl.Step>
  for +auto: List<&2, Nat>
  for w: {Tl.within(Tl.Step.effs(s), auto) == False{} : Bool}
  {Tl.exec(s <> post, auto, Nil{}) == Tl.Ran{Nil{}, Tl.Denied{Tl.Step.id(s)}} : Tl.Ran}

# ---- runners ----

# LAWS (G4): every runner of code goes through the gate. Each law is an
# open claim about the model in bend/runners.bend; PROOF.bend proves them
# (as Laws.<law>) with the lemmas of PROOF.bend section runners.

# (G4) Every runner of code goes through the gate
# -----------------------------------------------
# docs/tools.md S7, the model in bend/runners.bend. `Rn.registry` is the
# registry a session installs (crates/eukhe-core/src/durable/registry.rs);
# the bridge test in crates/eukhe-core/src/durable/runner/tests.rs dumps
# the real registry and runs the `ipython` gate on the scenarios of
# bend/bridge_runners.bend, and both must print what the model prints.

# LAW: every tool of a session's registry (with or without chat memory)
# that runs code that may run a program is gated
law gate_covers_every_runner:
  for +chat: Bool
  for +i: Nat
  for +t: Ru.Tool
  for at: {List.get(&2, Ru.Tool, Ru.registry(chat), i) == Some{t} : Maybe<&2, Ru.Tool>}
  for runs: {Ru.runs(t) == True{} : Bool}
  {Ru.gated(t) == True{} : Bool}

# LAW: the `ipython` tool runs code that may run a program, and the gate
# covers each of its calls
law ipython_gated_each_call:
  for +chat: Bool
  {Ru.find(Ru.registry(chat), "ipython") == Some{Ru.Tool{"ipython", [Ru.exec()], Ru.EachCall{}}} : Maybe<&2, Ru.Tool>}

# LAW: a gated call runs only when its caps are within the auto set or the
# user approves it
law cell_runs_only_within_or_approved:
  for +caps: List<&2, Nat>
  for +auto: List<&2, Nat>
  for +a: Ru.Asker
  for ran: {Ru.ran(Ru.cell(caps, auto, a)) == True{} : Bool}
  {Bool.or(Ru.within(caps, auto), Ru.Asker.yes(a)) == True{} : Bool}

# LAW: a call whose caps are within the auto set runs, unasked
law cell_within_runs_unasked:
  for +caps: List<&2, Nat>
  for +auto: List<&2, Nat>
  for a: Ru.Asker
  for free: {Ru.within(caps, auto) == True{} : Bool}
  {Ru.cell(caps, auto, a) == Ru.Out{False{}, Ru.Ran{Ru.Auto{}}} : Ru.Out}

# LAW: a call outside the auto set that the user approves runs, asked
law cell_approved_runs:
  for +caps: List<&2, Nat>
  for +auto: List<&2, Nat>
  for held: {Ru.within(caps, auto) == False{} : Bool}
  {Ru.cell(caps, auto, Ru.Says{True{}}) == Ru.Out{True{}, Ru.Ran{Ru.Approved{}}} : Ru.Out}

# LAW: a call outside the auto set without the user's approval (a denial,
# no answer, no client) does not run
law cell_no_yes_stops:
  for +caps: List<&2, Nat>
  for +auto: List<&2, Nat>
  for +a: Ru.Asker
  for held: {Ru.within(caps, auto) == False{} : Bool}
  for no: {Ru.Asker.yes(a) == False{} : Bool}
  {Ru.ran(Ru.cell(caps, auto, a)) == False{} : Bool}

# LAW: code that may run a program is never within an auto set without
# `exec`
law cell_exec_asks:
  for +caps: List<&2, Nat>
  for +auto: List<&2, Nat>
  for has: {Ru.elem(caps, Ru.exec()) == True{} : Bool}
  for lacks: {Ru.elem(auto, Ru.exec()) == False{} : Bool}
  {Ru.within(caps, auto) == False{} : Bool}

# ---- approvals ----

# LAWS (G5): a child's question reaches its root's user, a session that
# runs only from the phone gateway never waits, and the default auto set
# runs every step but the never-auto ones. Each law is an open claim about
# the model in bend/approvals.bend; PROOF.bend proves them (as Laws.<law>)
# with the lemmas of PROOF.bend section approvals.

# (G5) A child's question reaches its root's user
# ------------------------------------------------
# docs/tools.md G5, the model in bend/approvals.bend. A chain lists the
# sessions from the one that asks (a subagent, or a root) up to its root.
# The bridge test in crates/eukhe-daemon/src/shell_approval/bridge.rs
# runs the real approvals of a chain of sessions (clients attached or
# not, answering, denying or leaving, the phone gateway attached alone or
# beside them) on the scenarios of bend/bridge_approvals.bend, and both
# must print what the model prints.

# LAW: when no session below the root has clients that answer, a
# subagent's question reaches the root's clients, and their answer is the
# verdict
law child_answered_by_root:
  for +below: List<&2, Am.Desk>
  for quiet: {Am.quiet(below) == True{} : Bool}
  for +yes: Bool
  {Am.Out.end(Am.route(List.append(&2, Am.Desk, below, [Am.Says{yes}]))) == Am.Answered{List.length(&2, Am.Desk, below), yes} : Am.End}

# LAW: the first session up the chain whose clients answer gives the
# verdict, whatever the sessions above it
law nearest_answer_wins:
  for +below: List<&2, Am.Desk>
  for quiet: {Am.quiet(below) == True{} : Bool}
  for +yes: Bool
  for +above: List<&2, Am.Desk>
  {Am.Out.end(Am.route(List.append(&2, Am.Desk, below, Am.Says{yes} <> above))) == Am.Answered{List.length(&2, Am.Desk, below), yes} : Am.End}

# LAW: a question is unanswered (a denial) only when no session of the
# whole chain has clients that answer
law unanswered_only_when_quiet:
  for +ds: List<&2, Am.Desk>
  for none: {Am.Out.end(Am.route(ds)) == Am.Unanswered{} : Am.End}
  {Am.quiet(ds) == True{} : Bool}

# LAW: and then it is unanswered: no session invents an answer
law quiet_is_unanswered:
  for +ds: List<&2, Am.Desk>
  for quiet: {Am.quiet(ds) == True{} : Bool}
  {Am.Out.end(Am.route(ds)) == Am.Unanswered{} : Am.End}

# (G5) A session that runs only from the phone gateway never waits
# -----------------------------------------------------------------
# The phone gateway shows no question. A step is guarded when it writes a
# protected path (effect 5: eukhe's own config and credentials, a .git or
# .eukhe dir, a PATH dir) or reads or writes a secret (effect 6).

# LAW: a step of a session whose only clients are the phone gateway never
# waits: no client gets a frame, the question does not go up the chain,
# and the session's gateway rule answers at once
law gateway_never_waits:
  for +above: List<&2, Am.Desk>
  {Am.route(Am.Phone{} <> above) == Am.Out{Nil{}, Am.Ruled{0n}} : Am.Out}

# LAW: the gateway rule refuses a step that writes a protected path
law gateway_refuses_protected:
  for +es: List<&2, Nat>
  for protected: {Tl.elem(es, 5n) == True{} : Bool}
  for +above: List<&2, Am.Desk>
  {Am.fate(es, Am.Out.end(Am.route(Am.Phone{} <> above))) == Am.GatewayRefused{} : Am.Fate}

# LAW: the gateway rule refuses a step that reads or writes a secret
law gateway_refuses_secret:
  for +es: List<&2, Nat>
  for secret: {Tl.elem(es, 6n) == True{} : Bool}
  for +above: List<&2, Am.Desk>
  {Am.fate(es, Am.Out.end(Am.route(Am.Phone{} <> above))) == Am.GatewayRefused{} : Am.Fate}

# LAW: the gateway rule runs every other step unasked (a write, a run of
# a program, the network, a write outside the workspace)
law gateway_runs_the_rest:
  for +es: List<&2, Nat>
  for not_protected: {Tl.elem(es, 5n) == False{} : Bool}
  for not_secret: {Tl.elem(es, 6n) == False{} : Bool}
  for +above: List<&2, Am.Desk>
  {Am.fate(es, Am.Out.end(Am.route(Am.Phone{} <> above))) == Am.Runs{} : Am.Fate}

# LAW: a question the interactive clients leave unanswered while the
# phone gateway stays falls to the gateway rule, not up the chain
law left_to_the_gateway:
  for +above: List<&2, Am.Desk>
  {Am.route(Am.PhoneLeft{} <> above) == Am.Out{[0n], Am.Ruled{0n}} : Am.Out}

# LAW: a subagent's question that reaches a session whose only clients
# are the phone gateway (no session below it has clients that answer)
# fares as that session's own step: the same rule answers it
law gateway_rules_a_subagent:
  for +below: List<&2, Am.Desk>
  for quiet: {Am.quiet(below) == True{} : Bool}
  for +es: List<&2, Nat>
  for +above: List<&2, Am.Desk>
  {Am.fate(es, Am.Out.end(Am.route(List.append(&2, Am.Desk, below, Am.Phone{} <> above)))) == Am.fate(es, Am.Out.end(Am.route([Am.Phone{}]))) : Am.Fate}

# (G5) The default auto set; the never-auto effects
# --------------------------------------------------
# A step runs unasked when its effects are within the auto set
# (`shell.autoEffects`, bend/tools.bend `within`). The bridge test
# crates/eukhe-core/src/durable/shell/tests.rs
# `the_default_auto_set_is_its_model` reads the real auto set of a
# session with no settings and compares, with bend/bridge_approvals.bend,
# the effects it holds and `gate` on every step of one to seven effects.

# LAW: the auto set of a session whose user sets none holds exactly the
# grantable effects: read, write, exec and net
law default_auto_is_grantable:
  for +c: Nat
  {Tl.elem(Am.default_auto(), c) == Tl.grantable(c) : Bool}

# LAW: a step with an effect that no auto set may hold (4: a write
# outside the workspace, 5: a protected write, 6: a secret) never runs
# unasked through the auto set, in any session: its question goes its
# route
law never_auto_is_routed:
  for +auto: List<&2, Nat>
  for +es: List<&2, Nat>
  for +c: Nat
  for has: {Tl.elem(es, c) == True{} : Bool}
  for held: {Nat.is_le(4n, c) == True{} : Bool}
  for +ds: List<&2, Am.Desk>
  {Am.gate(auto, es, ds) == Am.routed(es, Am.route(ds)) : Am.Gated}

# LAW: so in a session whose client answers (the TUI, the dashboard), such
# a step asks that client, and its answer decides
law never_auto_asks_the_client:
  for +auto: List<&2, Nat>
  for +es: List<&2, Nat>
  for +c: Nat
  for has: {Tl.elem(es, c) == True{} : Bool}
  for held: {Nat.is_le(4n, c) == True{} : Bool}
  for +yes: Bool
  for +above: List<&2, Am.Desk>
  {Am.gate(auto, es, Am.Says{yes} <> above) == Am.Routed{Am.Out{[0n], Am.Answered{0n, yes}}, Am.yes.fate(yes)} : Am.Gated}

# LAW: in a session whose only clients are the phone gateway, a write
# outside the workspace that is not protected and touches no secret runs,
# and only by the gateway rule, never through the auto set
law outside_runs_only_by_the_gateway:
  for +auto: List<&2, Nat>
  for +es: List<&2, Nat>
  for outside: {Tl.elem(es, 4n) == True{} : Bool}
  for not_protected: {Tl.elem(es, 5n) == False{} : Bool}
  for not_secret: {Tl.elem(es, 6n) == False{} : Bool}
  for +above: List<&2, Am.Desk>
  {Am.gate(auto, es, Am.Phone{} <> above) == Am.Routed{Am.Out{Nil{}, Am.Ruled{0n}}, Am.Runs{}} : Am.Gated}

# LAW: and there a protected write or a secret is refused at once,
# whatever the auto set
law guarded_refused_from_the_phone:
  for +auto: List<&2, Nat>
  for +es: List<&2, Nat>
  for guarded: {Bool.or(Tl.elem(es, 5n), Tl.elem(es, 6n)) == True{} : Bool}
  for +above: List<&2, Am.Desk>
  {Am.gate(auto, es, Am.Phone{} <> above) == Am.Routed{Am.Out{Nil{}, Am.Ruled{0n}}, Am.GatewayRefused{}} : Am.Gated}

# ---- wire ----

# LAWS (the wire format of the compiled Bend core): every entry of
# bend/core.bend reads its input and writes its reply in the format of
# bend/wire.bend (grammar: crates/eukhe-bend/WIRE.md). Each law is an open
# claim about bend/wire.bend; PROOF.bend proves them (as Laws.<law>) with
# the lemmas of PROOF.bend section wire.
#
# R1: a decoder reads back what its encoder wrote, and leaves the input
#     after it untouched (so values compose: the laws quantify `rest`).
# R2: a decoder accepts only an encoder's output: any other input is
#     Bad{}, never a default (leading zeros, a missing ',', a short
#     string, a wrong count, an unknown char).
# R3: a Nat has at most 14 digits, decided while reading, so no input can
#     push a Nat past the runtime's 2^48-1 bound; a longer encoding is
#     refused, never misread.
# R4: no encoding starts with 'E', so a reply is either a value or the
#     error form 'E ' + text.

# Spec helpers
# ------------

# 1 + how many more decimal digits follow the lowest one of a value whose
# higher part is q (the fuel f >= q is enough)
def wire_digits.go(f: Nat, q: Nat) -> Nat:
  match f:
    case 0n:
      0n
    case 1n+g:
      match q:
        case 0n:
          0n
        case 1n+p:
          +m = {1n+p : Nat}
          1n+wire_digits.go(g, Nat.div(m, 10n))

# how many decimal digits n has (0 has one)
def wire_digits(n: Nat) -> Nat:
  +m = n
  1n+wire_digits.go(m, Nat.div(m, 10n))

# n fits the wire: at most 14 decimal digits
def wire_fits(n: Nat) -> Bool:
  Nat.is_le(wire_digits(n), 14n)

# every item of xs fits the wire
def wire_nats_fit(xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, t}:
      Bool.and(wire_fits(x), wire_nats_fit(t))

# s starts with the char 'E' (the error form of a reply)
def wire_opens_err(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      Char.is_eq(c, 'E')

# Nat
# ---

# LAW R1 a Nat that fits reads back, and the rest is untouched
# EXCLUDES: a misread digit, digits in the wrong order, a lost or eaten rest
law wire_nat_round_trip:
  for +n: Nat
  for rest: String
  for h: {wire_fits(n) == True{} : Bool}
  {Wr.get_nat(Wr.put_nat(n, rest)) == Wr.Got{n, rest} : Wr.Dec<Nat>}

# LAW R2 a decoded Nat is exactly an encoding: any other input is Bad{}
# EXCLUDES: leading zeros, a missing or another end mark, a default for
#   malformed input, a second spelling of a value
law wire_nat_exact:
  for +s: String
  for +n: Nat
  for +rest: String
  for h: {Wr.get_nat(s) == Wr.Got{n, rest} : Wr.Dec<Nat>}
  {s == Wr.put_nat(n, rest) : String}

# LAW R3 a decoded Nat fits: the decoder never reads a 15th digit
# EXCLUDES: a decoder that folds an unbounded digit string (and stops the
#   process past 2^48-1)
law wire_nat_decoded_fits:
  for +s: String
  for +n: Nat
  for +rest: String
  for h: {Wr.get_nat(s) == Wr.Got{n, rest} : Wr.Dec<Nat>}
  {wire_fits(n) == True{} : Bool}

# LAW R3 the encoding of a Nat too long for the wire is refused, not misread
# EXCLUDES: a truncated or wrapped value read from a long encoding
law wire_nat_too_long:
  for +n: Nat
  for rest: String
  for h: {wire_fits(n) == False{} : Bool}
  {Wr.get_nat(Wr.put_nat(n, rest)) == Wr.Bad{} : Wr.Dec<Nat>}

# LAW R3 witness: a Nat too long for the wire exists
# EXCLUDES: a vacuous wire_nat_too_long
law wire_too_long_exists:
  exs n: Nat
  {wire_fits(n) == False{} : Bool}

# LAW R4 no Nat encoding starts with 'E'
# EXCLUDES: a reply value read as the error form
law wire_nat_not_err:
  for n: Nat
  for rest: String
  {wire_opens_err(Wr.put_nat(n, rest)) == False{} : Bool}

# LAW R1 anchor: 42 is the digits 4 2 then ','
# EXCLUDES: a reversed, padded or unterminated spelling
law wire_nat_example:
  {Wr.put_nat(42n, "x") == "42,x" : String}

# LAW R1 anchor: 0 is one digit
# EXCLUDES: an empty spelling of 0
law wire_nat_zero_example:
  {Wr.put_nat(0n, "") == "0," : String}

# LAW R2 anchor: a leading zero is malformed
# EXCLUDES: a decoder that accepts 01 as 1
law wire_nat_leading_zero_example:
  {Wr.get_nat("01,") == Wr.Bad{} : Wr.Dec<Nat>}

# LAW R2 anchor: digits with no end mark are malformed
# EXCLUDES: a decoder that accepts the end of input as the end mark
law wire_nat_unterminated_example:
  {Wr.get_nat("12") == Wr.Bad{} : Wr.Dec<Nat>}

# LAW R3 the encoding of n spells wire_digits(n) digits, then ','
# EXCLUDES: a wire_digits that counts other than the digits the encoder
#   writes (the bound of R3 would then be off)
law wire_digits_spells:
  for +n: Nat
  {String.length(Wr.put_nat(n, "")) == 1n+wire_digits(n) : Nat}

# U32
# ---

# LAW R1 every U32 reads back, and the rest is untouched
# EXCLUDES: a U32 that wraps, loses high bits or eats the rest
law wire_u32_round_trip:
  for +x: U32
  for rest: String
  {Wr.get_u32(Wr.put_u32(x, rest)) == Wr.Got{x, rest} : Wr.Dec<U32>}

# LAW R2 a decoded U32 is exactly an encoding: any other input is Bad{}
# EXCLUDES: a Nat above 4294967295 read (wrapped) as a U32, a default for
#   malformed input
law wire_u32_exact:
  for +s: String
  for +x: U32
  for +rest: String
  for h: {Wr.get_u32(s) == Wr.Got{x, rest} : Wr.Dec<U32>}
  {s == Wr.put_u32(x, rest) : String}

# LAW R1 anchor: a small U32 is its decimal
# EXCLUDES: a U32 spelled in another base or width
law wire_u32_example:
  {Wr.put_u32(7, "") == "7," : String}

# Bool
# ----

# LAW R1 every Bool reads back, and the rest is untouched
# EXCLUDES: a swapped or constant Bool
law wire_bool_round_trip:
  for b: Bool
  for rest: String
  {Wr.get_bool(Wr.put_bool(b, rest)) == Wr.Got{b, rest} : Wr.Dec<Bool>}

# LAW R2 a decoded Bool is exactly an encoding: any other input is Bad{}
# EXCLUDES: any char other than T and F read as a Bool
law wire_bool_exact:
  for +s: String
  for +b: Bool
  for +rest: String
  for h: {Wr.get_bool(s) == Wr.Got{b, rest} : Wr.Dec<Bool>}
  {s == Wr.put_bool(b, rest) : String}

# LAW R4 no Bool encoding starts with 'E'
# EXCLUDES: a reply value read as the error form
law wire_bool_not_err:
  for b: Bool
  for rest: String
  {wire_opens_err(Wr.put_bool(b, rest)) == False{} : Bool}

# LAW R1 anchor: True is T
# EXCLUDES: another spelling of True
law wire_bool_example:
  {Wr.put_bool(True{}, "F") == "TF" : String}

# String
# ------

# LAW R1 a string whose length fits reads back, and the rest is untouched
# EXCLUDES: a length counted in another unit, a lost, added or changed char
law wire_str_round_trip:
  for +a: String
  for rest: String
  for h: {wire_fits(String.length(a)) == True{} : Bool}
  {Wr.get_str(Wr.put_str(a, rest)) == Wr.Got{a, rest} : Wr.Dec<String>}

# LAW R2 a decoded string is exactly an encoding: any other input is Bad{}
# EXCLUDES: a short string padded or accepted, a wrong length, a default
law wire_str_exact:
  for +s: String
  for +a: String
  for +rest: String
  for h: {Wr.get_str(s) == Wr.Got{a, rest} : Wr.Dec<String>}
  {s == Wr.put_str(a, rest) : String}

# LAW R1 anchor: the length counts chars, not bytes
# EXCLUDES: a length in UTF-8 bytes
law wire_str_example:
  {Wr.put_str("hé", "!") == "2,hé!" : String}

# Lists
# -----

# LAW R1 a list of Nats that fit, of a length that fits, reads back
# EXCLUDES: lost, added, reordered or misread items, a wrong count
law wire_list_round_trip:
  for +xs: List<&2, Nat>
  for rest: String
  for h: {Bool.and(wire_fits(List.length(&2, Nat, xs)), wire_nats_fit(xs)) == True{} : Bool}
  {Wr.get_list(~Nat, ~Wr.get_nat, Wr.put_list(~Nat, ~Wr.put_nat, xs, rest)) == Wr.Got{xs, rest} : Wr.Dec<List<&2, Nat>>}

# LAW R2 a decoded list is exactly an encoding: any other input is Bad{}
# EXCLUDES: a count larger than the items accepted, a default
law wire_list_exact:
  for +s: String
  for +xs: List<&2, Nat>
  for +rest: String
  for h: {Wr.get_list(~Nat, ~Wr.get_nat, s) == Wr.Got{xs, rest} : Wr.Dec<List<&2, Nat>>}
  {s == Wr.put_list(~Nat, ~Wr.put_nat, xs, rest) : String}

# LAW R1 anchor: a list is its count, then its items
# EXCLUDES: items with no count, a count after the items
law wire_list_example:
  {Wr.put_list(~Nat, ~Wr.put_nat, [1n, 22n], "") == "2,1,22," : String}

# Replies
# -------

# LAW R4 the error form is 'E ', then the text
# EXCLUDES: another error spelling the Rust Reader would read as a value
law wire_err_example:
  for text: String
  {Wr.err(text) == SCon{'E', SCon{' ', text}} : String}

# LAW R2 the end check is exactly "nothing is left"
# EXCLUDES: an entry that ignores input left over, or refuses a fully read
#   request
law wire_end_exact:
  for +s: String
  {Wr.end(s) == String.is_empty(s) : Bool}

# ---- retry ----

# LAWS (R, retries): when the harness sends a failed request again
# (audit H2, H3, H4, H5, H10, M3, M4). Each law is an open claim about
# the model in bend/retry.bend; PROOF.bend proves them (as Laws.<law>) with
# the lemmas of PROOF.bend section retry_policy. The Rust bridge tests run
# the real code against bend/bridge_retry.bend:
# crates/eukhe-core/src/durable/models/retry_bridge.rs the classifier, the
# wait and the failover walk; crates/eukhe-durable/src/harness/generation/
# retry_bridge.rs the deferred decisions, the stall and the idle deadline.

# (R1) The classifier
# -------------------
# crates/eukhe-ai/src/utils/retry.rs `FailureFacts::retryable`. Every
# input is free: any status, any kind, any text.

# LAW: a failure the quota park ended is never retried
law retry_never_parked:
  for limit: Bool
  for status: Maybe<&2, Nat>
  for kind: Maybe<&2, R.Cause>
  for text: Bool
  {R.retryable(R.Facts{True{}, limit, status, kind, text}) == False{} : Bool}

# LAW: a quota, billing or admission limit, or a refused server wait, is
# never retried
law retry_never_limit:
  for parked: Bool
  for status: Maybe<&2, Nat>
  for kind: Maybe<&2, R.Cause>
  for text: Bool
  {R.retryable(R.Facts{parked, True{}, status, kind, text}) == False{} : Bool}

# LAW: a recorded status below 500 that is not 408, 409 or 429 (a client
# error such as 400) is never retried, whatever the kind and the text say
law retry_never_client_error:
  for parked: Bool
  for limit: Bool
  for kind: Maybe<&2, R.Cause>
  for text: Bool
  for s: Nat
  for below: {Nat.is_lt(s, 500n) == True{} : Bool}
  for not408: {Nat.is_eq(s, 408n) == False{} : Bool}
  for not409: {Nat.is_eq(s, 409n) == False{} : Bool}
  for not429: {Nat.is_eq(s, 429n) == False{} : Bool}
  {R.retryable(R.Facts{parked, limit, Some{s}, kind, text}) == False{} : Bool}

# LAW: a retried failure that recorded a status recorded a server error
# or 408, 409 or 429
law retry_only_retryable:
  for parked: Bool
  for limit: Bool
  for kind: Maybe<&2, R.Cause>
  for text: Bool
  for s: Nat
  for retried: {R.retryable(R.Facts{parked, limit, Some{s}, kind, text}) == True{} : Bool}
  {Bool.or(Nat.is_ge(s, 500n), R.status.listed(s)) == True{} : Bool}

# LAW: a recorded status decides alone: the kind and the text change
# nothing
law retry_status_first:
  for parked: Bool
  for limit: Bool
  for s: Nat
  for k1: Maybe<&2, R.Cause>
  for t1: Bool
  for k2: Maybe<&2, R.Cause>
  for t2: Bool
  {R.retryable(R.Facts{parked, limit, Some{s}, k1, t1}) == R.retryable(R.Facts{parked, limit, Some{s}, k2, t2}) : Bool}

# LAW: with no status, a known kind decides alone: the text changes
# nothing
law retry_kind_before_text:
  for parked: Bool
  for limit: Bool
  for k: R.Cause
  for known: {R.Cause.known(k) == True{} : Bool}
  for t1: Bool
  for t2: Bool
  {R.retryable(R.Facts{parked, limit, None{}, Some{k}, t1}) == R.retryable(R.Facts{parked, limit, None{}, Some{k}, t2}) : Bool}

# LAW: a server error (status 500 or more) is retried when no park and no
# limit stop it
law retry_server_errors:
  for kind: Maybe<&2, R.Cause>
  for text: Bool
  for s: Nat
  for server: {Nat.is_lt(s, 500n) == False{} : Bool}
  {R.retryable(R.Facts{False{}, False{}, Some{s}, kind, text}) == True{} : Bool}

# (R2) The wait
# -------------
# crates/eukhe-ai/src/utils/retry.rs `RetryWait::of`.

# LAW: a retry never goes out before the server's requested wait
law retry_after_respected:
  for jitter: Nat
  for s: Nat
  for cap: Nat
  {R.Delay.respects(R.wait(jitter, Some{s}, cap), s) == True{} : Bool}

# LAW: a server wait above a cap refuses the retry and names the server's
# time
law retry_refuses_past_cap:
  for jitter: Nat
  for s: Nat
  for cap: Nat
  for capped: {Nat.is_gt(cap, 0n) == True{} : Bool}
  for over: {Nat.is_gt(s, cap) == True{} : Bool}
  {R.wait(jitter, Some{s}, cap) == R.Refused{s, cap} : R.Delay}

# (R3) The failover walk
# ----------------------
# crates/eukhe-core/src/durable/models/failover.rs `next_switch`. Every
# input is free: any chain, any failed attempts, any policy.

# LAW: a request goes back to a provider it tried only after it tried
# every provider of its chain
law failover_visits_once:
  for len: Nat
  for ts: List<&2, R.Tried>
  for p: R.Policy
  {R.Switch.fresh_first(R.next(len, ts, p), len, ts) == True{} : Bool}

# LAW: the next attempt never goes to the provider that just failed
law failover_never_twice_in_a_row:
  for len: Nat
  for ts: List<&2, R.Tried>
  for p: R.Policy
  {R.Switch.not_last(R.next(len, ts, p), ts) == True{} : Bool}

# LAW: a return to a provider the request tried waits a positive time,
# never less than the server's wait of that provider's last failure
law failover_return_waits:
  for len: Nat
  for ts: List<&2, R.Tried>
  for p: R.Policy
  {R.Switch.return_waits(R.next(len, ts, p), ts) == True{} : Bool}

# LAW: no switch waits longer than retry.failover.maxDelayMs
law failover_delay_capped:
  for len: Nat
  for ts: List<&2, R.Tried>
  for p: R.Policy
  {R.Switch.capped(R.next(len, ts, p), R.Policy.max(p)) == True{} : Bool}

# LAW: a request makes at most retry.failover.maxRetries switches
law failover_bounded:
  for len: Nat
  for ts: List<&2, R.Tried>
  for p: R.Policy
  {R.Switch.within(R.next(len, ts, p), ts, p) == True{} : Bool}

# (R4) The deferred job
# ---------------------
# crates/eukhe-durable/src/harness/generation/deferred.rs and the poll
# decisions of generation.rs `classify`. Every input is free: any
# replies, in any order.

# LAW: no request goes out while the request's deferred job is live: a
# failed poll polls the same job again or cancels it
law deferred_pays_once:
  for fails: Nat
  for budget: Nat
  for gots: List<&2, R.Got>
  {R.Tally.sends(R.run(fails, budget, gots)) == 0n : Nat}

# LAW: no poll goes out at or after the job's deadline
law deferred_bounded_in_time:
  for fails: Nat
  for budget: Nat
  for gots: List<&2, R.Got>
  {R.Tally.late(R.run(fails, budget, gots)) == 0n : Nat}

# LAW: a retryable failed poll, with fetch failures and time left, polls
# the same job again
law deferred_failed_poll_repolls:
  for fails: Nat
  for budget: Nat
  for failed: Nat
  for left: Nat
  for gap: Nat
  for below: {Nat.is_lt(failed, fails) == True{} : Bool}
  for live: {Nat.is_gt(left, 0n) == True{} : Bool}
  {R.step(fails, budget, R.Live{failed, left}, R.Broke{True{}, gap}) == R.Step{R.Poll{}, R.Live{1n+failed, Nat.sub(left, 1n+gap)}} : R.Step}

# (R5) The stall
# --------------
# crates/eukhe-durable/src/harness/generation/deferred.rs
# `idle_after_stall`.

# LAW: the retry of a stalled stream gets a longer idle deadline than the
# one it stalled under
law stall_retry_extends:
  for idle: Nat
  for positive: {Nat.is_gt(idle, 0n) == True{} : Bool}
  {Nat.is_lt(idle, R.stall.next(idle)) == True{} : Bool}

# (R6) The idle deadline
# ----------------------
# crates/eukhe-ai/src/utils/stream_idle.rs `StreamIdle::within`. Every
# input is free: any deadline, any gaps between the events.

# LAW: a watched stream ends no later than its last event before the
# deadline plus the deadline: a stall is detected in bounded time
law stall_detection_bounded:
  for gs: List<&2, Nat>
  for d: Nat
  {Nat.is_le(R.Idle.at(R.idle(gs, d)), Nat.add(R.idle.life(gs, d), d)) == True{} : Bool}

# LAW: a stream that sends no event ends as stalled at the deadline
law stall_silent_ends_at_deadline:
  for d: Nat
  {R.idle(Nil{}, d) == R.IdleStall{d} : R.Idle}

# ---- model_facts ----

# LAWS (S6.10): model and provider facts are data. A wire API decides a
# fact of a model only from the quirks rulebook's answer (and the model's
# explicit compat flag or the user's setting), the thinking budgets stay
# inside the model's limits, and where a fact moved from code into data the
# data gives the answers the code gave. Each law is an open claim about the
# model in bend/facts.bend; PROOF.bend proves them (as Laws.<law>)
# with the lemmas of PROOF.bend section facts; bend/bridge_facts.bend runs the
# model against the Rust code (crates/eukhe-core/src/durable/facts_bridge.rs).

# (S6.10.1) Decisions are rulebook lookups
# ----------------------------------------

# LAW: when a rule of a compiled rulebook applies to a model and no rule of
# a higher layer applies with its directive, the decision of that directive
# is the rule's value: the table decides, whatever the wire API's default
law facts_rulebook_decides:
  for +known: List<&2, Nat>
  for +pre: List<&2, If.Rule>
  for +r: If.Rule
  for +post: List<&2, If.Rule>
  for +q: If.Query
  for dflt: Bool
  for ok: {If.compiles(known, List.append(&2, If.Rule, pre, r <> post)) == True{} : Bool}
  for hit: {If.applies(q, r) == True{} : Bool}
  for top: {If.any_at(List.append(&2, If.Rule, pre, r <> post), q, If.Rule.dir(r), 1n+If.Rule.rank(r)) == False{} : Bool}
  {Fx.decide(List.append(&2, If.Rule, pre, r <> post), q, If.Rule.dir(r), dflt) == Nat.is_eq(If.Rule.val(r), 1n) : Bool}

# LAW: with no rule that applies, the decision is the wire API's stated
# default, never a guess from the model's id
law facts_rulebook_default:
  for +rs: List<&2, If.Rule>
  for +q: If.Query
  for +d: Nat
  for dflt: Bool
  for none: {If.any_at(rs, q, d, 0n) == False{} : Bool}
  {Fx.decide(rs, q, d, dflt) == dflt : Bool}

# LAW: two models with one rulebook answer get one decision: a model's id
# reaches a decision only through the rulebook
law facts_only_the_rulebook_decides:
  for +rs: List<&2, If.Rule>
  for +q1: If.Query
  for +q2: If.Query
  for +d: Nat
  for dflt: Bool
  for same: {If.lookup(rs, q1, d) == If.lookup(rs, q2, d) : If.Ans}
  {Fx.decide(rs, q1, d, dflt) == Fx.decide(rs, q2, d, dflt) : Bool}

# LAW: a model's explicit compat flag decides adaptive thinking, over the
# rulebook
law facts_adaptive_compat_first:
  for b: Bool
  for a: If.Ans
  {Fx.adaptive(Some{b}, a) == b : Bool}

# LAW: with no compat flag, adaptive thinking is the rulebook's answer,
# false where no rule applies; one rule for Anthropic Messages and Bedrock
law facts_adaptive_rulebook_second:
  for a: If.Ans
  {Fx.adaptive(None{}, a) == Fx.flag(a, False{}) : Bool}

# (S6.10.2) Budgets stay within the model's limits
# ------------------------------------------------

# LAW: a Google budget of a model with a budget rule is at most the rule's
# high budget, whatever the user's budgets
law facts_google_budget_at_most_high:
  for +b: Fx.Budgets
  for c: Fx.Customs
  for +l: Fx.Lv
  for +ordered: {Fx.Budgets.ordered(b) == True{} : Bool}
  {Nat.is_le(Fx.gtokens(b, c, l), Fx.Budgets.high(b)) == True{} : Bool}

# LAW: and at least the rule's minimal budget
law facts_google_budget_at_least_minimal:
  for +b: Fx.Budgets
  for c: Fx.Customs
  for +l: Fx.Lv
  for +ordered: {Fx.Budgets.ordered(b) == True{} : Bool}
  {Nat.is_le(Fx.Budgets.minimal(b), Fx.gtokens(b, c, l)) == True{} : Bool}

# LAW: with no user budget, a Google budget is the rule's budget of the
# level, unchanged: the rule is the table
law facts_google_rule_is_the_table:
  for +b: Fx.Budgets
  for +l: Fx.Lv
  for +ordered: {Fx.Budgets.ordered(b) == True{} : Bool}
  {Fx.gtokens(b, Fx.Customs.none(), l) == Fx.Budgets.at(b, l) : Nat}

# LAW: a fitted thinking budget is never above the response ceiling
law facts_fit_budget_under_ceiling:
  for +base: Maybe<&2, Nat>
  for +mm: Nat
  for +b: Nat
  for +a: Nat
  {Nat.is_le(Fx.Fit.budget(Fx.fit(base, mm, b, a)), Fx.Fit.max(Fx.fit(base, mm, b, a))) == True{} : Bool}

# LAW: and the response ceiling is never above the model's output cap
law facts_fit_ceiling_under_model:
  for +base: Maybe<&2, Nat>
  for +mm: Nat
  for +b: Nat
  for +a: Nat
  {Nat.is_le(Fx.Fit.max(Fx.fit(base, mm, b, a)), mm) == True{} : Bool}

# LAW: a budget capped for answer room leaves the answer its tokens under
# the ceiling
law facts_room_leaves_the_answer:
  for +b: Nat
  for +m: Nat
  for +a: Nat
  for fits: {Nat.is_le(a, m) == True{} : Bool}
  {Nat.is_le(Nat.add(Fx.room(b, m, a), a), m) == True{} : Bool}

# LAW: an auxiliary call's cap leaves its answer room over the thinking
# budget in use, whatever the user's budget
law facts_aux_cap_answer_room:
  for +b: Nat
  for +a: Nat
  {Nat.sub(Fx.aux_cap(b, a), b) == a : Nat}

# LAW: an unordered budget rule (a minimal, low, medium, high that falls
# somewhere) gives no Google budget: the rule is refused, never clamped
# into a range it does not have (Rust `u64::clamp` panicked on minimal >
# high); EXCLUDES: a budget from a rule with no range, a panic
law facts_google_unordered_refused:
  for +b: Fx.Budgets
  for c: Fx.Customs
  for l: Fx.Lv
  for bad: {Fx.Budgets.ordered(b) == False{} : Bool}
  {Fx.gbudget(Some{b}, c, l) == Fx.Unordered{} : Fx.GB}

# LAW: an ordered budget rule gives the budget gtokens (so every law on
# gtokens holds for the Google budget)
law facts_google_ordered_tokens:
  for +b: Fx.Budgets
  for c: Fx.Customs
  for +l: Fx.Lv
  for ok: {Fx.Budgets.ordered(b) == True{} : Bool}
  {Fx.gbudget(Some{b}, c, l) == Fx.Tokens{Fx.gtokens(b, c, l)} : Fx.GB}

# x held inside lo..hi: never below lo, never above hi
def budgets.held(x: Nat, +lo: Nat, +hi: Nat) -> Nat:
  Nat.max(lo, Nat.min(x, hi))

# LAW: a Google budget under a rule is the user's budget of the level,
# else the rule's, held inside the rule's minimal..high: a user's budget
# inside the range is sent as it is; EXCLUDES: a user's budget ignored, a
# budget moved inside the range
law facts_google_budget_held:
  for +b: Fx.Budgets
  for c: Fx.Customs
  for +l: Fx.Lv
  for +ordered: {Fx.Budgets.ordered(b) == True{} : Bool}
  {Fx.gtokens(b, c, l) == budgets.held(Maybe.default(&2, Nat, Fx.Customs.at(c, l), Fx.Budgets.at(b, l)), Fx.Budgets.minimal(b), Fx.Budgets.high(b)) : Nat}

# LAW: without a rule, a Google budget is the user's budget of the level
law facts_google_free_user:
  for c: Fx.Customs
  for l: Fx.Lv
  for n: Nat
  for u: {Fx.Customs.at(c, l) == Some{n} : Maybe<&2, Nat>}
  {Fx.gbudget(None{}, c, l) == Fx.Tokens{n} : Fx.GB}

# LAW: without a rule and a user's budget, the Google budget is dynamic
law facts_google_free_dynamic:
  for c: Fx.Customs
  for l: Fx.Lv
  for u: {Fx.Customs.at(c, l) == None{} : Maybe<&2, Nat>}
  {Fx.gbudget(None{}, c, l) == Fx.Dynamic{} : Fx.GB}

# LAW: the budget level of a request's level: each level keeps its own,
# xhigh and max take high
law facts_budget_levels:
  {[Fx.Lv.of(Fx.EMinimal{}), Fx.Lv.of(Fx.ELow{}), Fx.Lv.of(Fx.EMedium{}), Fx.Lv.of(Fx.EHigh{}), Fx.Lv.of(Fx.EXhigh{}), Fx.Lv.of(Fx.EMax{})] == [Fx.Minimal{}, Fx.Low{}, Fx.Medium{}, Fx.High{}, Fx.High{}, Fx.High{}] : List<&2, Fx.Lv>}

# LAW: the budget of a level is the user's budget of the level, over the
# defaults
law facts_budget_user_first:
  for c: Fx.Customs
  for d: Fx.Budgets
  for +l: Fx.Lv
  for n: Nat
  for u: {Fx.Customs.at(c, l) == Some{n} : Maybe<&2, Nat>}
  {Fx.budget(c, d, l) == n : Nat}

# LAW: without the user's budget, the budget of a level is the default
law facts_budget_default:
  for c: Fx.Customs
  for d: Fx.Budgets
  for +l: Fx.Lv
  for u: {Fx.Customs.at(c, l) == None{} : Maybe<&2, Nat>}
  {Fx.budget(c, d, l) == Fx.Budgets.at(d, l) : Nat}

# the fit of the response ceiling m: the budget b, capped so that a
# tokens stay for the answer when it fills the ceiling
def budgets.fit.at(over: Bool, +m: Nat, +b: Nat, +a: Nat) -> Fx.Fit:
  match over:
    case True{}:
      Fx.Fit{m, Nat.min(b, Nat.sub(m, a))}
    case False{}:
      Fx.Fit{m, b}

def budgets.fit(+m: Nat, +b: Nat, +a: Nat) -> Fx.Fit:
  budgets.fit.at(Nat.is_le(m, b), m, b, a)

# LAW: with the caller's cap x, the ceiling is x plus the budget, at most
# the model's cap, and the budget is capped for answer room when it fills
# the ceiling; EXCLUDES: any other ceiling or budget (the two laws above
# only bound them)
law facts_fit_exact_caller:
  for +x: Nat
  for +mm: Nat
  for +b: Nat
  for +a: Nat
  {Fx.fit(Some{x}, mm, b, a) == budgets.fit(Nat.min(Nat.add(x, b), mm), b, a) : Fx.Fit}

# LAW: without the caller's cap, the ceiling is the model's cap
law facts_fit_exact_model:
  for +mm: Nat
  for +b: Nat
  for +a: Nat
  {Fx.fit(None{}, mm, b, a) == budgets.fit(mm, b, a) : Fx.Fit}

# LAW (the Nat range): a caller's cap at or above the model's cap fits as
# no cap, so the cap Rust saturates at the wire's largest Nat (10^14-1)
# fits as it did unsaturated whenever the model's cap is below it
law facts_fit_saturated_caller:
  for +x: Nat
  for +mm: Nat
  for +b: Nat
  for +a: Nat
  for +above: {Nat.is_le(mm, x) == True{} : Bool}
  {Fx.fit(Some{x}, mm, b, a) == Fx.fit(None{}, mm, b, a) : Fx.Fit}

# LAW (the Nat range): two budgets at or above the model's cap fit alike,
# so a budget Rust saturates at the wire's largest Nat fits as it did
# unsaturated whenever the model's cap is below it
law facts_fit_saturated_budget:
  for +base: Maybe<&2, Nat>
  for +mm: Nat
  for +b1: Nat
  for +b2: Nat
  for +a: Nat
  for +h1: {Nat.is_le(mm, b1) == True{} : Bool}
  for +h2: {Nat.is_le(mm, b2) == True{} : Bool}
  {Fx.fit(base, mm, b1, a) == Fx.fit(base, mm, b2, a) : Fx.Fit}

# LAW (the Nat range): the compactor's cap is the thinking budget plus the
# answer, at most top (Rust passes the wire's largest Nat): below top
# the answer keeps its room exactly (facts_aux_cap_answer_room), at top
# the cap saturates as Rust's `saturating_add` does
law facts_aux_cap_within:
  for +b: Nat
  for +a: Nat
  for +top: Nat
  {Fx.aux_cap.within(b, a, top) == Nat.min(Fx.aux_cap(b, a), top) : Nat}

# (S6.10.3) Oracles: the data gives the answers the code gave
# -----------------------------------------------------------

# LAW: the Bedrock effort from the thinking-level map is the effort of the
# old id list, for every model whose map keeps the catalog's promise (a
# native-xhigh model's map sends xhigh at xhigh)
law facts_bedrock_effort_oracle:
  for native: Bool
  for +m: Fx.EMap
  for +l: Fx.ELv
  for ok: {Fx.native_ok(native, m) == True{} : Bool}
  {Fx.effort.old(native, m, l) == Fx.effort(m, l) : Nat}

# LAW: the budget of budget-based Claude from the rulebook's default
# budgets is the budget of the old Bedrock table, for every user budget
law facts_bedrock_budget_oracle:
  for c: Fx.Customs
  for +l: Fx.Lv
  {Fx.budget(c, Fx.budgets.shipped(), l) == Fx.budget.old(c, l) : Nat}

# (S6.10.4) Prices are data
# -------------------------

# LAW: a price row of the model wins over the row of every model: the
# gpt-5.5 priority price is a row, not an id test in code
law facts_tier_price_model_row_first:
  for +rows: List<&2, Fx.PRow>
  for +m: Nat
  for +t: Nat
  for +k: Nat
  for hit: {Fx.price.find(rows, m, t, True{}) == Some{k} : Maybe<&2, Nat>}
  {Fx.price(rows, m, t) == Some{k} : Maybe<&2, Nat>}

# LAW: a tier that no row prices leaves the base price (a provider that does
# not sell the tier is not billed OpenAI's multiplier)
law facts_tier_price_no_row_base:
  for +rows: List<&2, Fx.PRow>
  for +m: Nat
  for +t: Nat
  for +base: Nat
  for none: {Fx.price(rows, m, t) == None{} : Maybe<&2, Nat>}
  {Fx.tier_cost(base, Fx.price(rows, m, t)) == Nat.mul(base, 100n) : Nat}

# LAW: the shipped OpenAI rows give the multiplier of the old OpenAI
# function for every model and tier
law facts_tier_price_openai_oracle:
  for m: Nat
  for t: Nat
  {Maybe.default(&2, Nat, Fx.price(Fx.prices.openai(), m, t), 100n) == Fx.price.old.openai(m, t) : Nat}

# LAW: the shipped Codex rows give the multiplier of the old Codex
# function for every model and tier
law facts_tier_price_codex_oracle:
  for m: Nat
  for t: Nat
  {Maybe.default(&2, Nat, Fx.price(Fx.prices.codex(), m, t), 100n) == Fx.price.old.codex(m, t) : Nat}

# LAW: a 1h cache write of a model that no row prices costs the model's own
# cache write rate, never a price borrowed from another provider
law facts_cache_write_1h_own_rate:
  for +input: Nat
  for +write: Nat
  {Fx.rate_1h(None{}, input, write) == write : Nat}

# ---- dashboard_auth ----

# LAWS (D1): the dashboard's pairing gate. Each law is an open claim about
# the model in bend/dash.bend; PROOF.bend proves them (as Laws.<law>)
# with the lemmas of PROOF.bend section dashboard_auth.

# (D1) Pairing
# ------------
# docs/dashboard.md "Pairing", the model in bend/dash.bend; the Rust gate
# (crates/eukhe-dashboard/src/pairing.rs, http.rs, bridge.rs) and the
# model run the same events in the bridge test
# pairing::tests::the_gate_pairs_as_its_model. Every input is free: any
# state, any connection, any token, any events before and after.

# LAW: a frame runs (a daemon command) only when its connection holds the
# current token
law dash_frame_runs_only_current:
  for +s: Da.St
  for +c: Nat
  for ran: {Da.ran(c, Da.out(s, Da.Frame{c})) == True{} : Bool}
  {Da.held(c, Da.St.conns(s)) == Some{Da.St.cur(s)} : Maybe<&2, Nat>}

# LAW: a frame of a connection that holds the current token runs
law dash_current_frame_runs:
  for +s: Da.St
  for +c: Nat
  for cur: {Da.held(c, Da.St.conns(s)) == Some{Da.St.cur(s)} : Maybe<&2, Nat>}
  {Da.out(s, Da.Frame{c}) == Da.Ran{c} : Da.Out}

# LAW: a connection pairs only when it presents the current token
law dash_open_pairs_only_current:
  for +s: Da.St
  for +c: Nat
  for +shown: Maybe<&2, Nat>
  for paired: {Da.is_paired(Da.out(s, Da.Open{c, shown})) == True{} : Bool}
  {shown == Some{Da.St.cur(s)} : Maybe<&2, Nat>}

# LAW: a connection that presents the current token pairs
law dash_current_open_pairs:
  for +s: Da.St
  for +c: Nat
  {Da.out(s, Da.Open{c, Some{Da.St.cur(s)}}) == Da.Paired{c} : Da.Out}

# LAW: a paired connection holds the token it presented
law dash_paired_holds_token:
  for +s: Da.St
  for +c: Nat
  {Da.held(c, Da.St.conns(Da.next(s, Da.Open{c, Some{Da.St.cur(s)}}))) == Some{Da.St.cur(s)} : Maybe<&2, Nat>}

# LAW: a connection that is not open runs no frame, whatever comes, until
# it opens again
law dash_closed_runs_nothing:
  for +s: Da.St
  for +c: Nat
  for +evs: List<&2, Da.Ev>
  for closed: {Da.held(c, Da.St.conns(s)) == None{} : Maybe<&2, Nat>}
  for again: {Da.any_opens(c, evs) == False{} : Bool}
  {Da.any_ran(c, Da.run(evs, s)) == False{} : Bool}

# LAW: a rejected connection runs no frame, whatever comes, until it
# opens again
law dash_rejected_runs_nothing:
  for +s: Da.St
  for +c: Nat
  for +shown: Maybe<&2, Nat>
  for +evs: List<&2, Da.Ev>
  for rejected: {Da.is_paired(Da.out(s, Da.Open{c, shown})) == False{} : Bool}
  for again: {Da.any_opens(c, evs) == False{} : Bool}
  {Da.any_ran(c, Da.run(Da.Open{c, shown} <> evs, s)) == False{} : Bool}

# LAW: after any history, a rotation ends every connection: none runs a
# frame, whatever comes, until it opens again
law dash_rotation_ends_connections:
  for +hist: List<&2, Da.Ev>
  for +c: Nat
  for +evs: List<&2, Da.Ev>
  for again: {Da.any_opens(c, evs) == False{} : Bool}
  {Da.any_ran(c, Da.run(Da.Rotate{} <> evs, Da.state(hist, Da.init()))) == False{} : Bool}

# LAW: after any history, a rotation invalidates every token made before
# it: an open that presents one is rejected, whatever comes after
law dash_rotation_rejects_old_tokens:
  for +hist: List<&2, Da.Ev>
  for +more: List<&2, Da.Ev>
  for +c: Nat
  for +t: Nat
  for old: {Nat.is_le(t, Da.St.cur(Da.state(hist, Da.init()))) == True{} : Bool}
  {Da.out(Da.state(Da.Rotate{} <> more, Da.state(hist, Da.init())), Da.Open{c, Some{t}}) == Da.Rejected{c} : Da.Out}

# ---- documents ----

# LAWS: the documents tools (crates/eukhe-docs and the documents tools of
# crates/eukhe-core): edits, writes, moves, temporary files, line endings,
# tags, seen lines, grep and glob. Each law is an open claim about a model
# in bend/doc_*.bend; PROOF.bend proves them (as Laws.<law>) with the
# lemmas of PROOF.bend section documents and, for lines and their endings,
# PROOF.bend section doc_lines. A Rust bridge test runs the real
# code and the model on the same generated scenarios and requires the same
# transcript.

# (F1, F9) An edit of many files
# ------------------------------
# bend/doc_commit.bend: every input is free: any files, each an update or
# a move, changed since the edit staged it or not, with any fault (none,
# a failed directory sync, a failed publish, a failed source removal).

# LAW: the reply calls a file applied exactly when its new content is on
# disk: after a conflict, a publish that fails at any file, or a publish
# that lands with a warning
law edit_reports_what_landed:
  for +fs: List<&2, Cm.Doc>
  {Cm.reported(Cm.reply(fs)) == Cm.landed(fs) : List<&2, Nat>}

# LAW: when one file changed since the edit staged it, no file lands
law edit_all_or_nothing_on_conflict:
  for +pre: List<&2, Cm.Doc>
  for +k: Cm.Op
  for +x: Cm.Fault
  for +post: List<&2, Cm.Doc>
  {Cm.landed(List.append(&2, Cm.Doc, pre, Cm.Doc{k, True{}, x} <> post)) == Nil{} : List<&2, Nat>}

# LAW: an edit with no changed file and no failed publish lands every
# file
law edit_lands_every_file:
  for +fs: List<&2, Cm.Doc>
  for same: {Cm.conflict(fs) == False{} : Bool}
  for sound: {Cm.failing(fs) == False{} : Bool}
  {Cm.landed(fs) == Cm.ids(fs, 0n) : List<&2, Nat>}

# (F2) The write tool
# -------------------
# bend/doc_commit.bend: every input is free: any disk (a version or no
# file), any versions the session saw, any new content.

# LAW: a write over a version the session did not see is refused and
# changes nothing: a write never loses a change the session did not see
law write_never_loses_unseen:
  for +d: Maybe<&2, Nat>
  for +s: List<&2, Nat>
  for +c: Nat
  for lost: {Cm.unseen(d, s) == True{} : Bool}
  {Cm.write(d, s, c) == Cm.Wt{False{}, d, s} : Cm.Wt}

# LAW: a write over no file or over a version the session saw writes,
# and the session then knows the new version
law write_writes_seen:
  for +d: Maybe<&2, Nat>
  for +s: List<&2, Nat>
  for +c: Nat
  for kept: {Cm.unseen(d, s) == False{} : Bool}
  {Cm.write(d, s, c) == Cm.Wt{True{}, Some{c}, Cm.saw(c, s)} : Cm.Wt}

# (F5) A move
# -----------
# bend/doc_commit.bend: every input is free: any files with any names
# and contents, any source and destination names.

# LAW: a move to a name that a file has is refused and changes nothing:
# an MV never replaces a file
law move_never_overwrites:
  for +s: Nat
  for +t: Nat
  for +es: List<&2, Cm.Entry>
  for taken: {Cm.has(t, es) == True{} : Bool}
  {Cm.move(s, t, es) == Cm.Mv{False{}, es} : Cm.Mv}

# LAW: a move of a file to a free name moves it: the move is done, the
# source name is gone, and the destination holds the source's content
law move_moves:
  for +s: Nat
  for +t: Nat
  for +es: List<&2, Cm.Entry>
  for free: {Cm.has(t, es) == False{} : Bool}
  for from: {Cm.has(s, es) == True{} : Bool}
  {Cm.Mv.ok(Cm.move(s, t, es)) == True{} : Bool} & {Cm.has(s, Cm.Mv.es(Cm.move(s, t, es))) == False{} : Bool} & {Cm.get(t, Cm.Mv.es(Cm.move(s, t, es))) == Cm.get(s, es) : Maybe<&2, Nat>}

# (F10) Temporary files
# ---------------------
# bend/doc_commit.bend: every input is free: any entries in the target's
# directory (a temporary file of the target, of another target, or
# another file), held by a live writer or not.

# LAW: a sweep never removes a temporary file that a live writer holds
law temp_sweep_never_held:
  for +pre: List<&2, Cm.Temp>
  for +i: Nat
  for +k: Cm.Sort
  for +post: List<&2, Cm.Temp>
  {Cm.sweep(List.append(&2, Cm.Temp, pre, Cm.Temp{i, k, True{}} <> post)) == List.append(&2, Cm.Temp, Cm.sweep(pre), Cm.sweep(post)) : List<&2, Cm.Temp>}

# LAW: a sweep never removes a temporary file of another target, or a
# file that is not a temporary file
law temp_sweep_only_own:
  for +pre: List<&2, Cm.Temp>
  for +i: Nat
  for +k: Cm.Sort
  for +h: Bool
  for +post: List<&2, Cm.Temp>
  for other: {Cm.Sort.own(k) == False{} : Bool}
  {Cm.sweep(List.append(&2, Cm.Temp, pre, Cm.Temp{i, k, h} <> post)) == List.append(&2, Cm.Temp, Cm.sweep(pre), Cm.sweep(post)) : List<&2, Cm.Temp>}

# LAW: a sweep removes every temporary file of the target that no live
# writer holds
law temp_sweep_removes_free:
  for +pre: List<&2, Cm.Temp>
  for +i: Nat
  for +post: List<&2, Cm.Temp>
  {Cm.sweep(List.append(&2, Cm.Temp, pre, Cm.Temp{i, Cm.Own{}, False{}} <> post)) == List.append(&2, Cm.Temp, Cm.sweep(pre), Cm.Temp{i, Cm.Own{}, False{}} <> Cm.sweep(post)) : List<&2, Cm.Temp>}

# (F4) Lines and their endings
# ----------------------------
# bend/doc_lines.bend: every input is free: any body of bytes (content,
# `\r`, `\n` in any order), with or without a BOM; any edit that replaces
# any run of whole lines with any new lines.

# LAW: a file loaded and persisted with no edit is the same bytes: every
# line keeps its own ending, a lone `\r` stays content, the BOM stays
law load_persist_roundtrip:
  for +f: Dl.Doc
  {Dl.persist(Dl.load(f)) == f : Dl.Doc}

# LAW: an edit of the lines [s, s+k) keeps every byte outside them: the
# bytes of the lines before s, and the bytes after line s+k (its later
# lines with their own endings, and the last piece), are the same in the
# persisted file
law edit_keeps_untouched_bytes:
  for +bom: Bool
  for +bs: List<&2, Dl.B>
  for +s: Nat
  for +k: Nat
  for +xs: List<&2, List<&2, Dl.B>>
  for fits: {Nat.is_le(Nat.add(s, k), Dl.lfs(bs)) == True{} : Bool}
  exs x: List<&2, Dl.B>
  {Dl.persist(Dl.edit(Dl.load(Dl.Doc{bom, bs}), s, k, xs)) == Dl.Doc{bom, List.append(&2, Dl.B, Dl.upto(bs, s), List.append(&2, Dl.B, x, Dl.from(bs, Nat.add(s, k))))} : Dl.Doc}

# LAW: grep and read number the lines of a text the same way and show
# the same text for each line (a text that is not empty: grep shows no
# row of an empty text, read shows one empty row)
law grep_line_is_read_line:
  for +b: Dl.B
  for +bs: List<&2, Dl.B>
  {Dl.grep_rows(b <> bs) == Dl.read_rows(b <> bs) : List<&2, List<&2, Dl.B>>}

# the n copies of x
def lines.Rep(-A: Data, n: Nat, +x: A) -> List<&2, A>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      x <> lines.Rep(A, m, x)

# the ending of the origin of each line, from its runs
def lines.Ends(rs: List<&2, Dl.Run>) -> List<&2, Maybe<&2, Dl.End>>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> rest:
      match r:
        case Dl.Run{o, n}:
          List.append(&2, Maybe<&2, Dl.End>, lines.Rep(Maybe<&2, Dl.End>, n, o), lines.Ends(rest))

# the separator after each line, from its runs
def lines.Flat(ss: List<&2, Dl.Seps>) -> List<&2, Dl.End>:
  match ss:
    case Nil{}:
      Nil{}
    case s <> rest:
      match s:
        case Dl.Seps{e, n}:
          List.append(&2, Dl.End, lines.Rep(Dl.End, n, e), lines.Flat(rest))

# the separator after each line: the ending of its origin, else the
# separator written before it (c before the first line)
def lines.Carry(ens: List<&2, Maybe<&2, Dl.End>>, +c: Dl.End) -> List<&2, Dl.End>:
  match ens:
    case Nil{}:
      Nil{}
    case o <> rest:
      match o:
        case None{}:
          c <> lines.Carry(rest, c)
        case Some{+e}:
          e <> lines.Carry(rest, e)

def lines.Owns.go(rest: List<&2, Dl.Piece>, p: Dl.Piece) -> List<&2, Maybe<&2, Dl.End>>:
  match rest:
    case Nil{}:
      Nil{}
    case q <> more:
      match p:
        case Dl.Piece{t, en}:
          en <> lines.Owns.go(more, q)

# the own ending of each piece but the last
def lines.Owns(ps: List<&2, Dl.Piece>) -> List<&2, Maybe<&2, Dl.End>>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> rest:
      lines.Owns.go(rest, p)

def lines.Weave.go(rest: List<&2, Dl.Piece>, p: Dl.Piece, ss: List<&2, Dl.End>) -> List<&2, Dl.B>:
  match rest:
    case Nil{}:
      match p:
        case Dl.Piece{t, en}:
          t
    case q <> more:
      match p:
        case Dl.Piece{t, en}:
          match ss:
            case Nil{}:
              List.append(&2, Dl.B, t, lines.Weave.go(more, q, Nil{}))
            case s <> st:
              List.append(&2, Dl.B, t, List.append(&2, Dl.B, Dl.ebytes(s), lines.Weave.go(more, q, st)))

# the bytes of the pieces, each but the last followed by its separator
# from ss
def lines.Weave(ps: List<&2, Dl.Piece>, ss: List<&2, Dl.End>) -> List<&2, Dl.B>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> rest:
      lines.Weave.go(rest, p, ss)

# LAW: persist writes each piece, and after each piece but the last the
# separator that the carry rule gives: its own ending, else the one
# written before it
# EXCLUDES: a persist whose separators follow another rule than the plan
# the Rust weaves with
law persist_weaves_carry:
  for +ps: List<&2, Dl.Piece>
  for +c: Dl.End
  {Dl.start(ps, c) == lines.Weave(ps, lines.Carry(lines.Owns(ps), c)) : List<&2, Dl.B>}

# LAW: the plan over runs gives, line for line, the separators of the
# carry rule
# EXCLUDES: a lost or doubled line in a run, a run that does not move the
# carry, an empty run that moves it, a new line that takes LF instead of
# the carry
# LEAVES FREE: where the answer splits its runs (Rust reads them line by
# line)
law persist_plan_refines:
  for +rs: List<&2, Dl.Run>
  for +c: Dl.End
  {lines.Flat(Dl.plan(rs, c)) == lines.Carry(lines.Ends(rs), c) : List<&2, Dl.End>}

# LAW anchor: two CRLF lines, three new lines (they take CRLF), an LF
# line, an empty run, a new line (it takes LF)
# EXCLUDES: new lines that take LF or the file's first ending
law persist_plan_example:
  {Dl.plan([Dl.Run{Some{Dl.CrLf{}}, 2n}, Dl.Run{None{}, 3n}, Dl.Run{Some{Dl.Lf{}}, 1n}, Dl.Run{Some{Dl.CrLf{}}, 0n}, Dl.Run{None{}, 1n}], Dl.Lf{}) == [Dl.Seps{Dl.CrLf{}, 2n}, Dl.Seps{Dl.CrLf{}, 3n}, Dl.Seps{Dl.Lf{}, 1n}, Dl.Seps{Dl.Lf{}, 1n}] : List<&2, Dl.Seps>}

# a run of lines fits the wire: its length does
def lines.RunFit(r: Dl.Run) -> Bool:
  match r:
    case Dl.Run{o, n}:
      wire_fits(n)

def lines.RunsFit(rs: List<&2, Dl.Run>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case r <> rest:
      Bool.and(lines.RunFit(r), lines.RunsFit(rest))

# every number of a request of the plan fits the wire
def lines.WireFits(+rs: List<&2, Dl.Run>) -> Bool:
  Bool.and(wire_fits(List.length(&2, Dl.Run, rs)), lines.RunsFit(rs))

# LAW: the plan's entry of the compiled core answers, for every request
# whose numbers fit the wire, the encoding of the model's separators
# EXCLUDES: a codec that loses, reorders or misreads a run or the carry
law lines_entry_refines:
  for +rs: List<&2, Dl.Run>
  for +c: Dl.End
  for h: {lines.WireFits(rs) == True{} : Bool}
  {Fdl.ffi(Fdl.put_req(rs, c, "")) == Wr.put_list(~Dl.Seps, ~Fdl.put_seps, Dl.plan(rs, c), "") : String}

# LAW anchor: an unknown ending tag answers the error form
# EXCLUDES: a default ending for a request the entry could not read
law lines_entry_rejects_example:
  {Fdl.ffi("0,2,") == Wr.err("doc_lines: malformed carry") : String}

# LAW witness: a request of the plan fits the wire (lines_entry_refines is
# not vacuous)
# EXCLUDES: a vacuous lines_entry_refines
law lines_wire_fits_example:
  {lines.WireFits([Dl.Run{Some{Dl.CrLf{}}, 3n}, Dl.Run{None{}, 1n}]) == True{} : Bool}

# (F3) Tags
# ---------
# bend/doc_tags.bend: every input is free: any text, any lines shown, a
# read or a grep, and any text the file holds when grep records its
# result.

# LAW: the tag of a read or grep result names the text its rows come
# from: the tag is the identity of that text, and every row (n, x) is
# line n of it
law tag_names_shown_text:
  for +t: List<&2, Nat>
  for +op: Dt.Op
  {Dt.Shown.tag(Dt.show(t, op)) == t : List<&2, Nat>} & {Dt.from_text(t, Dt.Shown.rows(Dt.show(t, op))) == True{} : Bool}


# (F11) Seen lines
# ----------------
# bend/doc_seen.bend: every input is free: any seen lines of a snapshot
# tagged by a read or a mismatch error (any runs of lines, so any set of
# lines), any anchors, each with any width of its line in the snapshot
# or no line there (line 0, past the end).

# line n is in the run iv: lo <= n <= hi
def seen.Inside(+n: Nat, iv: Ds.Iv) -> Bool:
  match iv:
    case Ds.Iv{lo, hi}:
      Bool.and(Nat.is_le(lo, n), Nat.is_le(n, hi))

# line n is seen: some run of ivs holds it
def seen.In(+n: Nat, ivs: List<&2, Ds.Iv>) -> Bool:
  match ivs:
    case Nil{}:
      False{}
    case iv <> rest:
      Bool.or(seen.Inside(n, iv), seen.In(n, rest))

# every line of xs is seen
def seen.Sub(xs: List<&2, Nat>, +ivs: List<&2, Ds.Iv>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> rest:
      Bool.and(seen.In(x, ivs), seen.Sub(rest, ivs))

# each line of xs as a run of one line
def seen.Points(xs: List<&2, Nat>) -> List<&2, Ds.Iv>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> rest:
      Ds.Iv{x, x} <> seen.Points(rest)

# the anchors of ats whose line is not seen, in order
def seen.Unseen.keep(+a: Ds.At, rest: List<&2, Ds.At>, s: Bool) -> List<&2, Ds.At>:
  match s:
    case True{}:
      rest
    case False{}:
      a <> rest

def seen.Unseen(+seen: List<&2, Ds.Iv>, ats: List<&2, Ds.At>) -> List<&2, Ds.At>:
  match ats:
    case Nil{}:
      Nil{}
    case +a <> rest:
      seen.Unseen.keep(a, seen.Unseen(seen, rest), seen.In(Ds.At.line(a), seen))

# a line of this width is shown whole: the snapshot has the line, and it
# has at most `cols` characters
def seen.Fit(w: Maybe<&2, Nat>) -> Bool:
  match w:
    case None{}:
      False{}
    case Some{x}:
      Nat.is_le(x, Ds.cols)

# every anchor in us is shown whole
def seen.Fits(us: List<&2, Ds.At>) -> Bool:
  match us:
    case Nil{}:
      True{}
    case a <> rest:
      match a:
        case Ds.At{n, w}:
          Bool.and(seen.Fit(w), seen.Fits(rest))

# a rejection shows every anchor in us whole: at most `cap` of them, each
# shown whole
def seen.Whole(+us: List<&2, Ds.At>) -> Bool:
  Bool.and(Nat.is_le(List.length(&2, Ds.At, us), Ds.cap), seen.Fits(us))

# how a line is shown: whole (None), or its first `cols` characters
def seen.Cut(whole: Bool) -> Maybe<&2, Nat>:
  match whole:
    case True{}:
      None{}
    case False{}:
      Some{Ds.cols}

def seen.Shown.at(+n: Nat, w: Maybe<&2, Nat>, rest: List<&2, Ds.Show>) -> List<&2, Ds.Show>:
  match w:
    case None{}:
      rest
    case Some{x}:
      Ds.Show{n, seen.Cut(Nat.is_le(x, Ds.cols))} <> rest

# the lines a rejection shows for the anchors in us: each anchor that is
# a line of the snapshot, in order, cut when it is longer than `cols`
def seen.Shown(us: List<&2, Ds.At>) -> List<&2, Ds.Show>:
  match us:
    case Nil{}:
      Nil{}
    case a <> rest:
      match a:
        case Ds.At{n, w}:
          seen.Shown.at(n, w, seen.Shown(rest))

def seen.After.go(whole: Bool, u: List<&2, Ds.Iv>, seen: List<&2, Ds.Iv>) -> List<&2, Ds.Iv>:
  match whole:
    case True{}:
      List.append(&2, Ds.Iv, u, seen)
    case False{}:
      seen

# the seen lines after an edit whose unseen anchors are us: they join
# the seen lines when the rejection showed them whole, else nothing
# changes (and an edit with no unseen anchor changes nothing)
def seen.After(+seen: List<&2, Ds.Iv>, +us: List<&2, Ds.At>) -> List<&2, Ds.Iv>:
  seen.After.go(seen.Whole(us), seen.Points(Ds.lines(us)), seen)

# LAW: an edit applies only when every anchor is a seen line: a line
# number the model never saw is never an address
# EXCLUDES: an edit that applies on an unseen anchor (a guard that skips
# anchors, or only checks the first)
law edit_only_seen_lines:
  for +seen: List<&2, Ds.Iv>
  for +ats: List<&2, Ds.At>
  for ok: {Ds.Step.applied(Ds.edit(seen, ats)) == True{} : Bool}
  {seen.Sub(Ds.lines(ats), seen) == True{} : Bool}

# LAW: an edit whose anchors are all seen applies (the guard rejects
# nothing more)
# EXCLUDES: a guard that rejects a seen anchor (always-reject)
law edit_seen_applies:
  for +seen: List<&2, Ds.Iv>
  for +ats: List<&2, Ds.At>
  for all: {seen.Sub(Ds.lines(ats), seen) == True{} : Bool}
  {Ds.Step.applied(Ds.edit(seen, ats)) == True{} : Bool}

# LAW: a rejected edit with at most `cap` anchors applies on a straight
# retry exactly when every unseen anchor is a line of the snapshot of at
# most `cols` characters (the rejection showed it whole); else the retry
# is rejected again and the model must read
# EXCLUDES: a reveal that does not mark its lines seen (a retry loop),
# a retry that applies on a line the rejection never showed whole
law reveal_then_retry:
  for +seen: List<&2, Ds.Iv>
  for +ats: List<&2, Ds.At>
  for few: {Nat.is_le(List.length(&2, Ds.At, ats), Ds.cap) == True{} : Bool}
  {Ds.Step.applied(Ds.edit(Ds.Step.seen(Ds.edit(seen, ats)), ats)) == seen.Fits(seen.Unseen(seen, ats)) : Bool}

# LAW: after any edit, the unseen anchors join the seen lines exactly
# when the rejection showed them whole (at most `cap`, each a line of at
# most `cols` characters); else the seen lines stay as they were
# EXCLUDES: marking seen a line past the end or a line shown cut, a
# reveal that marks nothing, a reveal past `cap`
law edit_marks_whole_reveal:
  for +seen: List<&2, Ds.Iv>
  for +ats: List<&2, Ds.At>
  {Ds.Step.seen(Ds.edit(seen, ats)) == seen.After(seen, seen.Unseen(seen, ats)) : List<&2, Ds.Iv>}

# LAW: the guard names exactly the anchors that are not seen, in order
# (none: the edit applies)
# EXCLUDES: naming a seen anchor, dropping an unseen one
law reject_names_unseen:
  for +seen: List<&2, Ds.Iv>
  for +ats: List<&2, Ds.At>
  {Ds.Check.unseen(Ds.check(seen, ats)) == Ds.lines(seen.Unseen(seen, ats)) : List<&2, Nat>}

# LAW: a rejection shows, of its first `cap` unseen anchors, each one
# that is a line of the snapshot, in order, cut to `cols` characters
# when it is longer
# EXCLUDES: showing a seen line, a line past the end, more than `cap`
# lines, a long line whole, a short line cut
law reject_shows_lines:
  for +seen: List<&2, Ds.Iv>
  for +ats: List<&2, Ds.At>
  {Ds.Check.shown(Ds.check(seen, ats)) == seen.Shown(List.take(&2, Ds.At, seen.Unseen(seen, ats), Ds.cap)) : List<&2, Ds.Show>}

# LAW: a rejection says it showed its unseen anchors whole exactly when
# they are at most `cap` and each is a line of at most `cols` characters
# EXCLUDES: a reveal called whole with a line missing or cut
law reject_whole_exact:
  for +seen: List<&2, Ds.Iv>
  for +ats: List<&2, Ds.At>
  {Ds.Check.whole(Ds.check(seen, ats)) == seen.Whole(seen.Unseen(seen, ats)) : Bool}

# LAW anchor: line 1 is seen; line 2 is past the end, line 3 is longer
# than 512 characters, line 4 has exactly 512
# EXCLUDES: a misread of `cols` (512 shown cut, 513 whole) or of "past
# the end"
law reveal_example:
  {Ds.check([Ds.Iv{1n, 1n}], [Ds.At{1n, Some{3n}}, Ds.At{2n, None{}}, Ds.At{3n, Some{513n}}, Ds.At{4n, Some{512n}}]) == Ds.Check{[2n, 3n, 4n], [Ds.Show{3n, Some{512n}}, Ds.Show{4n, None{}}], False{}} : Ds.Check}

# LAW: witness: an edit with at most `cap` anchors exists, so
# reveal_then_retry is not vacuous
# EXCLUDES: a vacuous reveal_then_retry
law retry_few_witness:
  exs ats: List<&2, Ds.At>
  {Nat.is_le(List.length(&2, Ds.At, ats), Ds.cap) == True{} : Bool}

# LAW anchor: a rejection of lines that are shown whole marks them seen,
# and the retry applies
# EXCLUDES: a retry that the whole reveal does not let through
law retry_applies_example:
  {Ds.Step.applied(Ds.edit(Ds.Step.seen(Ds.edit([Ds.Iv{1n, 1n}], [Ds.At{1n, Some{3n}}, Ds.At{2n, Some{512n}}])), [Ds.At{1n, Some{3n}}, Ds.At{2n, Some{512n}}])) == True{} : Bool}

# LAW anchor: a rejection with a line past the end marks nothing seen,
# and the retry is rejected again
# EXCLUDES: marking seen a line the snapshot does not have
law retry_rejected_example:
  {Ds.Step.applied(Ds.edit(Ds.Step.seen(Ds.edit([Ds.Iv{1n, 1n}], [Ds.At{2n, Some{3n}}, Ds.At{9n, None{}}])), [Ds.At{2n, Some{3n}}, Ds.At{9n, None{}}])) == False{} : Bool}

# LAW anchor on the seen runs: the guard finds a line inside a run, at
# either end of it, in any run; and not a line between runs, past the
# last, or in an empty run (hi < lo)
# EXCLUDES: a membership that ignores lo or hi, reads only the first
# run, or counts an empty run
law seen_runs_example:
  {Ds.Check.unseen(Ds.check([Ds.Iv{9n, 2n}, Ds.Iv{1n, 3n}, Ds.Iv{7n, 9n}], [Ds.At{1n, None{}}, Ds.At{2n, None{}}, Ds.At{3n, None{}}, Ds.At{4n, None{}}, Ds.At{6n, None{}}, Ds.At{7n, None{}}, Ds.At{8n, None{}}, Ds.At{9n, None{}}, Ds.At{10n, None{}}])) == [4n, 6n, 10n] : List<&2, Nat>}

# LAW: a rejection shows at most 40 unseen anchors, and a line of at most
# 512 characters whole (the single source of both numbers: the Rust
# renders what `check` answers)
# EXCLUDES: a changed reveal cap or column limit
law reveal_bounds:
  {Ds.cap == 40n : Nat} & {Ds.cols == 512n : Nat}

# a run fits the wire: both ends do
def seen.IvFit(iv: Ds.Iv) -> Bool:
  match iv:
    case Ds.Iv{lo, hi}:
      Bool.and(wire_fits(lo), wire_fits(hi))

def seen.IvsFit(ivs: List<&2, Ds.Iv>) -> Bool:
  match ivs:
    case Nil{}:
      True{}
    case iv <> rest:
      Bool.and(seen.IvFit(iv), seen.IvsFit(rest))

# an anchor fits the wire: its line, and its width when it has one
def seen.AtFit(a: Ds.At) -> Bool:
  match a:
    case Ds.At{n, w}:
      match w:
        case None{}:
          wire_fits(n)
        case Some{x}:
          Bool.and(wire_fits(n), wire_fits(x))

def seen.AtsFit(ats: List<&2, Ds.At>) -> Bool:
  match ats:
    case Nil{}:
      True{}
    case a <> rest:
      Bool.and(seen.AtFit(a), seen.AtsFit(rest))

# every number of a request of the guard fits the wire (Rust saturates a
# width at the wire's bound, and a line number is a u32)
def seen.WireFits(+seen: List<&2, Ds.Iv>, +ats: List<&2, Ds.At>) -> Bool:
  Bool.and(Bool.and(wire_fits(List.length(&2, Ds.Iv, seen)), seen.IvsFit(seen)), Bool.and(wire_fits(List.length(&2, Ds.At, ats)), seen.AtsFit(ats)))

# LAW: the guard's entry of the compiled core answers, for every request
# whose numbers fit the wire, the encoding of the model's verdict
# EXCLUDES: a codec that loses, invents, reorders or misreads a seen run
# or an anchor, an entry that answers a default or another rule
law seen_entry_refines:
  for +seen: List<&2, Ds.Iv>
  for +ats: List<&2, Ds.At>
  for h: {seen.WireFits(seen, ats) == True{} : Bool}
  {Fds.ffi(Fds.put_req(seen, ats, "")) == Fds.put_check(Ds.check(seen, ats), "") : String}

# LAW anchor: a malformed request answers the error form, and a request
# with input left over too
# EXCLUDES: a default verdict for a request the entry could not read
law seen_entry_rejects_example:
  {Fds.ffi("1,1,") == Wr.err("doc_seen: malformed seen runs") : String} & {Fds.ffi("0,0,x") == Wr.err("doc_seen: input left over") : String}

# LAW witness: a request of the guard fits the wire (seen_entry_refines
# is not vacuous)
# EXCLUDES: a vacuous seen_entry_refines
law seen_wire_fits_example:
  {seen.WireFits([Ds.Iv{1n, 3n}], [Ds.At{2n, Some{80n}}, Ds.At{9n, None{}}]) == True{} : Bool}

# (F6) What grep searched
# -----------------------
# bend/doc_search.bend: every input is free: any walk (text files with
# any number of matches, over the size limit or not; binary files, files
# that do not open, excluded directories, symlinks, walk errors, in any
# order), any match cap of a file, any total match cap, any page.

# LAW: every walked entry is in exactly one class (no match, shown,
# paged out, not searched, or skipped with its reason): the classes add
# up to the walk
law grep_accounts_every_file:
  for +es: List<&2, Sr.Ent>
  for +p: Nat
  for +s: Nat
  for +k: Nat
  for +rem: Nat
  for +n: Nat
  {Sr.Count.total(Sr.account(Sr.run(es, p, s, k, rem, n))) == List.length(&2, Sr.Ent, es) : Nat}

# LAW: a result has the notice of a class of entries it did not search,
# skipped, or searched only in part exactly when that class is not empty
law grep_notes_every_gap:
  for +os: List<&2, Sr.Out>
  for +t: Sr.Note
  {Sr.noted(t, os) == Bool.not(Nat.is_eq(Sr.Note.count(Sr.account(os), t), 0n)) : Bool}

# LAW: a shown file whose matches were cut has its own notice
law grep_notes_every_cut:
  for +pre: List<&2, Sr.Out>
  for +i: Nat
  for +pa: Bool
  for +post: List<&2, Sr.Out>
  {Sr.mem(i, Sr.cuts(List.append(&2, Sr.Out, pre, Sr.Out{i, Sr.Shown{}, True{}, pa} <> post))) == True{} : Bool}

# (F7) Continuations
# ------------------
# bend/doc_search.bend: every input is free: any ordered list (the
# matching files of grep, the ranked paths of glob), any skip, any page
# size, and the continuation the page gives.

# LAW: a continuation gives a page that is not empty
law continuation_progresses:
  for +ps: List<&2, Nat>
  for +s: Nat
  for +k: Nat
  for +c: Nat
  for h: {Sr.next(ps, s, k) == Some{c} : Maybe<&2, Nat>}
  {List.is_empty(&2, Nat, Sr.page(ps, c, k)) == False{} : Bool}

# LAW: a page and the page of its continuation are, together, the start
# of the list after the skip: nothing left out between them, nothing
# twice
law continuation_contiguous:
  for +ps: List<&2, Nat>
  for +s: Nat
  for +k: Nat
  for +c: Nat
  for h: {Sr.next(ps, s, k) == Some{c} : Maybe<&2, Nat>}
  exs rest: List<&2, Nat>
  {List.append(&2, Nat, Sr.page(ps, s, k), List.append(&2, Nat, Sr.page(ps, c, k), rest)) == List.drop(&2, Nat, ps, s) : List<&2, Nat>}

# LAW: in a list with no item twice, a page and the page of its
# continuation have no item in common
law continuation_disjoint:
  for +ps: List<&2, Nat>
  for +s: Nat
  for +k: Nat
  for +c: Nat
  for +x: Nat
  for h: {Sr.next(ps, s, k) == Some{c} : Maybe<&2, Nat>}
  for nd: {Sr.nodup(ps) == True{} : Bool}
  {Bool.and(Sr.mem(x, Sr.page(ps, s, k)), Sr.mem(x, Sr.page(ps, c, k))) == False{} : Bool}

# ---- config ----

# LAWS (config audit H1-H4, M3, M7): no config input is lost in silence.
# A writer never replaces a document it could not read and keeps every
# entry it does not change; a setter writes the document on disk, not
# the copy it loaded; each leaf of a settings document applies or is
# named; a malformed limit fails closed; a saved default model runs or
# its substitution is shown; an untrusted project changes no limit,
# prompt or credential; a project MCP entry never takes the keys of a
# global one. Each law is an open claim about the models in
# bend/config.bend and bend/default_model.bend; PROOF.bend proves them
# (as Laws.<law>) with the lemmas of PROOF.bend section config.

# (H1) A read/modify/write of a config document
# ---------------------------------------------
# settings.json (`eukhe mcp add`, the resource arrays, every setter),
# mcp-connections.json (`remove`, verify) and auth.json (`set`,
# `remove`): the writer reads the document under its lock.

# LAW: a document that could not be read or parsed (or has a version
# the writer does not know) is never written
law rmw_refuses_broken:
  for e: Cf.Edit
  {Cf.rmw(Cf.Broken{}, e) == Cf.Refused{} : Cf.Write}

# LAW: when it writes, every key the edit does not touch keeps the value
# it had in the document read
law rmw_keeps_others:
  for +d: List<&2, Cf.Entry>
  for +e: Cf.Edit
  for +j: Nat
  for +h: {Cf.touches(e, j) == False{} : Bool}
  {Cf.kept(Cf.rmw(Cf.Parsed{d}, e), j) == Cf.lookup(d, j) : Maybe<&2, Nat>}

# LAW: the key the edit sets has the value it sets
law rmw_applies_change:
  for +d: List<&2, Cf.Entry>
  for +k: Nat
  for +v: Nat
  {Cf.kept(Cf.rmw(Cf.Parsed{d}, Cf.Set{k, v}), k) == Some{v} : Maybe<&2, Nat>}

# (H2) A settings setter
# ----------------------

# LAW: a setter of key k to v writes D[k := v], where D is the document
# on disk at write time, whatever copy the setter loaded before (a copy
# without a key that failed to load, or without a key another writer
# added since)
law settings_save_preserves:
  for loaded: List<&2, Cf.Entry>
  for d: List<&2, Cf.Entry>
  for +k: Nat
  for v: Nat
  {Cf.save(loaded, Cf.Parsed{d}, k, v) == Cf.Wrote{Cf.set(d, k, v)} : Cf.Write}

# (H3) The leaves of a settings document
# --------------------------------------
# settings.json, through the leaf load (`settings::load`): the same
# report path as config.cfg (`CvarError`, a settings-error row).

# LAW: every leaf applies or is named by a diagnostic
law leaf_applied_or_reported:
  for ls: List<&2, Cf.Leaf>
  for +l: Cf.Leaf
  for i: Cf.In(l, ls)
  {Bool.or(Cf.listed(Cf.applied(ls), Cf.Leaf.path(l)), Cf.listed(Cf.reported(ls), Cf.Leaf.path(l))) == True{} : Bool}

# LAW: of distinct leaves, none both applies and is named
law leaf_not_both:
  for ls: List<&2, Cf.Leaf>
  for +n: Nat
  for +d: {Cf.distinct(ls) == True{} : Bool}
  {Bool.and(Cf.listed(Cf.applied(ls), n), Cf.listed(Cf.reported(ls), n)) == False{} : Bool}

# LAW: a malformed in-flight limit never reads as no limit: it caps its
# provider at 1 (a value that is not a map caps every provider)
law limit_malformed_fails_closed:
  for s: Cf.InFlight
  for +p: Nat
  for h: {Cf.malformed_at(s, p) == True{} : Bool}
  {Cf.limit(s, p) == Cf.Cap{1n} : Cf.Lim}

# LAW: a well-formed entry is the provider's limit
law limit_number_applies:
  for es: List<&2, Cf.Slot>
  for +p: Nat
  for +n: Nat
  for h: {Cf.slot(es, p) == Some{Cf.Num{n}} : Maybe<&2, Cf.Val>}
  {Cf.limit(Cf.Entries{es}, p) == Cf.val_limit(Cf.Num{n}) : Cf.Lim}

# (H4) The saved default model
# ----------------------------
# bend/default_model.bend: the session-model resolution at open.

# LAW: a session started with a saved default runs on it, or its notices
# name the saved default and the reason it did not run
law default_honoured_or_reported:
  for x: Dm.In
  {Dm.reported(x, Dm.open(Dm.resolve(x))) == True{} : Bool}

# LAW: a session that runs on its saved default has no notice
law default_quiet_when_honoured:
  for x: Dm.In
  for h: {Dm.on_saved(Dm.Session.run(Dm.open(Dm.resolve(x)))) == True{} : Bool}
  {Dm.none(Dm.Session.notes(Dm.open(Dm.resolve(x)))) == True{} : Bool}

# LAW: with no saved default the session has no notice
law default_quiet_when_unset:
  for cat: Bool
  for key: Bool
  for out: Bool
  for next: Dm.Next
  {Dm.Session.notes(Dm.open(Dm.resolve(Dm.In{Dm.NoDefault{}, cat, key, out, next}))) == Nil{} : List<&2, Dm.Key>}

# LAW: a saved default whose provider has no credentials opens the
# session with no model: no other provider runs in its place
law default_unkeyed_never_moves:
  for m: Nat
  for out: Bool
  for next: Dm.Next
  {Dm.Session.run(Dm.open(Dm.resolve(Dm.In{Dm.Default{m}, True{}, False{}, out, next}))) == Dm.Idle{} : Dm.Run}

# The laws below pin every answer of the resolver (Dm.resolve, the Rust
# `resolve_session_model` with no requested model), case by case: nothing
# saved; the catalog, the credentials and the scope, in this order; the
# chain's pick or none.

# LAW: with nothing saved the chain's pick runs, with nothing to say
# EXCLUDES: a notice or a substitution invented for an unset default, the
#   chain's pick ignored
law default_unset_runs_pick:
  for cat: Bool
  for key: Bool
  for out: Bool
  for n: Nat
  {Dm.resolve(Dm.In{Dm.NoDefault{}, cat, key, out, Dm.Next{n}}) == Dm.Runs{Dm.Other{n}, Dm.Kept{}} : Dm.Res}

# LAW: with nothing saved and no model to pick there is no model, and no
# error
# EXCLUDES: a typed error for an unset default
law default_unset_without_pick:
  for cat: Bool
  for key: Bool
  for out: Bool
  {Dm.resolve(Dm.In{Dm.NoDefault{}, cat, key, out, Dm.NoNext{}}) == Dm.Nothing{} : Dm.Res}

# LAW: a saved default in the catalog, with credentials and in the scope,
# runs, with nothing to say
# EXCLUDES: a usable saved default replaced by the chain's pick
law default_usable_runs:
  for m: Nat
  for next: Dm.Next
  {Dm.resolve(Dm.In{Dm.Default{m}, True{}, True{}, False{}, next}) == Dm.Runs{Dm.Saved{}, Dm.Kept{}} : Dm.Res}

# LAW: a saved default the catalog lacks gives way to the chain's pick,
# which names it with the reason "not in the catalog"
# EXCLUDES: a wrong reason, a silent substitution, the credentials or
#   the scope checked before the catalog
law default_uncatalogued_swaps:
  for m: Nat
  for key: Bool
  for out: Bool
  for n: Nat
  {Dm.resolve(Dm.In{Dm.Default{m}, False{}, key, out, Dm.Next{n}}) == Dm.Runs{Dm.Other{n}, Dm.Swapped{Dm.K{m, Dm.NotInCatalog{}}}} : Dm.Res}

# LAW: a saved default the catalog lacks, with no model to pick, is the
# typed error with the reason "not in the catalog"
# EXCLUDES: no model and no error (a silent idle session)
law default_uncatalogued_refused:
  for m: Nat
  for key: Bool
  for out: Bool
  {Dm.resolve(Dm.In{Dm.Default{m}, False{}, key, out, Dm.NoNext{}}) == Dm.Refused{Dm.K{m, Dm.NotInCatalog{}}} : Dm.Res}

# LAW: a saved default whose provider has no credentials is the typed
# error with the reason "no credentials", whatever the scope and the
# chain's pick
# EXCLUDES: a move to another provider, a wrong reason
law default_unkeyed_refused:
  for m: Nat
  for out: Bool
  for next: Dm.Next
  {Dm.resolve(Dm.In{Dm.Default{m}, True{}, False{}, out, next}) == Dm.Refused{Dm.K{m, Dm.NoCredentials{}}} : Dm.Res}

# LAW: a saved default outside the set scope gives way to the chain's
# pick, which names it with the reason "not in the scope"
# EXCLUDES: a silent substitution, a wrong reason
law default_unscoped_swaps:
  for m: Nat
  for n: Nat
  {Dm.resolve(Dm.In{Dm.Default{m}, True{}, True{}, True{}, Dm.Next{n}}) == Dm.Runs{Dm.Other{n}, Dm.Swapped{Dm.K{m, Dm.NotInScope{}}}} : Dm.Res}

# LAW: a saved default outside the set scope, with no model to pick, is
# the typed error with the reason "not in the scope"
# EXCLUDES: no model and no error
law default_unscoped_refused:
  for m: Nat
  {Dm.resolve(Dm.In{Dm.Default{m}, True{}, True{}, True{}, Dm.NoNext{}}) == Dm.Refused{Dm.K{m, Dm.NotInScope{}}} : Dm.Res}

# (M3) An untrusted project
# -------------------------

# LAW: an untrusted project changes no limit, system prompt or
# credential: a key that no preference item of the project sets keeps
# its global value
law untrusted_changes_nothing_guarded:
  for +g: List<&2, Cf.Entry>
  for items: List<&2, Cf.Item>
  for +k: Nat
  for +h: {Cf.only_guarded(items, k) == True{} : Bool}
  {Cf.lookup(Cf.effective(Cf.Untrusted{}, g, items), k) == Cf.lookup(g, k) : Maybe<&2, Nat>}

# LAW: a trusted project's item applies, whatever it is
law trusted_project_applies:
  for g: List<&2, Cf.Entry>
  for +k: Nat
  for kind: Cf.Class
  for v: Nat
  for items: List<&2, Cf.Item>
  {Cf.lookup(Cf.effective(Cf.Trusted{}, g, Cf.Item{k, kind, v} <> items), k) == Some{v} : Maybe<&2, Nat>}

# (M7) Named entries
# ------------------

# LAW: a project MCP entry is the entry that applies, whole: it never
# takes a key (a URL, a credential) from the global entry of its name
law project_entry_never_merges:
  for +g: List<&2, Cf.Named>
  for p: List<&2, Cf.Named>
  for +n: Nat
  for h: {Cf.has(p, n) == True{} : Bool}
  {Cf.find(Cf.merge(g, p), n) == Cf.find(p, n) : Maybe<&2, List<&2, Cf.Entry>>}

# LAW: a global entry the project does not name stays whole
law global_entry_kept:
  for +g: List<&2, Cf.Named>
  for p: List<&2, Cf.Named>
  for +n: Nat
  for h: {Cf.has(p, n) == False{} : Bool}
  {Cf.find(Cf.merge(g, p), n) == Cf.find(g, n) : Maybe<&2, List<&2, Cf.Entry>>}

# The wire codec of bend/ffi_default_model.bend (grammar: that file's
# header, crates/eukhe-bend/WIRE.md). R1: the request and every reply
# read back; R2: a well-formed request answers the resolver's answer
# (Dm.resolve), encoded; R3: a malformed or overlong request answers the
# error form, never a model. Every input is free.

# what fits the wire: every Nat at most 14 digits
def dmw_saved_fits(x: Dm.Saved) -> Bool:
  match x:
    case Dm.NoDefault{}:
      True{}
    case Dm.Default{m}:
      wire_fits(m)

def dmw_next_fits(x: Dm.Next) -> Bool:
  match x:
    case Dm.NoNext{}:
      True{}
    case Dm.Next{n}:
      wire_fits(n)

def dmw_in_fits(x: Dm.In) -> Bool:
  match x:
    case Dm.In{saved, cat, key, out, next}:
      Bool.and(dmw_saved_fits(saved), dmw_next_fits(next))

def dmw_key_fits(k: Dm.Key) -> Bool:
  match k:
    case Dm.K{m, r}:
      wire_fits(m)

def dmw_pick_fits(p: Dm.Pick) -> Bool:
  match p:
    case Dm.Saved{}:
      True{}
    case Dm.Other{n}:
      wire_fits(n)

def dmw_sub_fits(s: Dm.Sub) -> Bool:
  match s:
    case Dm.Kept{}:
      True{}
    case Dm.Swapped{k}:
      dmw_key_fits(k)

def dmw_res_fits(r: Dm.Res) -> Bool:
  match r:
    case Dm.Runs{p, s}:
      Bool.and(dmw_pick_fits(p), dmw_sub_fits(s))
    case Dm.Nothing{}:
      True{}
    case Dm.Refused{k}:
      dmw_key_fits(k)

# LAW R1 a reason reads back, and the rest is untouched
# EXCLUDES: one reason read as another
law dmw_reason_round_trip:
  for r: Dm.Reason
  for rest: String
  {FDm.get_reason(FDm.put_reason(r, rest)) == Wr.Got{r, rest} : Wr.Dec<Dm.Reason>}

# LAW R1 a saved default that fits reads back
# EXCLUDES: no default read as one, a misread model
law dmw_saved_round_trip:
  for +x: Dm.Saved
  for rest: String
  for h: {dmw_saved_fits(x) == True{} : Bool}
  {FDm.get_saved(FDm.put_saved(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Dm.Saved>}

# LAW R1 the chain's pick that fits reads back
# EXCLUDES: no pick read as one, a misread model
law dmw_next_round_trip:
  for +x: Dm.Next
  for rest: String
  for h: {dmw_next_fits(x) == True{} : Bool}
  {FDm.get_next(FDm.put_next(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Dm.Next>}

# LAW R1 a request that fits reads back
# EXCLUDES: a fact (catalog, credentials, scope) lost, swapped or misread
law dmw_in_round_trip:
  for +x: Dm.In
  for rest: String
  for h: {dmw_in_fits(x) == True{} : Bool}
  {FDm.get_in(FDm.put_in(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Dm.In>}

# LAW R1 a notice's key that fits reads back
# EXCLUDES: the model or the reason lost or misread
law dmw_key_round_trip:
  for +k: Dm.Key
  for rest: String
  for h: {dmw_key_fits(k) == True{} : Bool}
  {FDm.get_key(FDm.put_key(k, rest)) == Wr.Got{k, rest} : Wr.Dec<Dm.Key>}

# LAW R1 a pick that fits reads back
# EXCLUDES: the saved default read as another model, or the reverse
law dmw_pick_round_trip:
  for +p: Dm.Pick
  for rest: String
  for h: {dmw_pick_fits(p) == True{} : Bool}
  {FDm.get_pick(FDm.put_pick(p, rest)) == Wr.Got{p, rest} : Wr.Dec<Dm.Pick>}

# LAW R1 a substitution that fits reads back
# EXCLUDES: a swap read as kept (a silent substitution), or the reverse
law dmw_sub_round_trip:
  for +s: Dm.Sub
  for rest: String
  for h: {dmw_sub_fits(s) == True{} : Bool}
  {FDm.get_sub(FDm.put_sub(s, rest)) == Wr.Got{s, rest} : Wr.Dec<Dm.Sub>}

# LAW R1 the reply, a resolution that fits, reads back
# EXCLUDES: a refusal read as a run or as no model, a field lost
law dmw_res_round_trip:
  for +r: Dm.Res
  for rest: String
  for h: {dmw_res_fits(r) == True{} : Bool}
  {FDm.get_res(FDm.put_res(r, rest)) == Wr.Got{r, rest} : Wr.Dec<Dm.Res>}

# LAW R2 an encoded request answers the resolver's answer, encoded
# EXCLUDES: an entry that resolves other than Dm.resolve, or drops a fact
#   on the way in or out
law dmw_answers:
  for +x: Dm.In
  for h: {dmw_in_fits(x) == True{} : Bool}
  {FDm.ffi(FDm.put_in(x, "")) == FDm.put_res(Dm.resolve(x), "") : String}

# LAW R3 a malformed request answers the error form
# EXCLUDES: a default model for a request it cannot read
law dmw_malformed:
  for +s: String
  for h: {FDm.get_in(s) == Wr.Bad{} : Wr.Dec<Dm.In>}
  {FDm.ffi(s) == Wr.err("default_model: malformed request") : String}

# LAW R3 a request with input left over answers the error form
# EXCLUDES: an entry that answers a request followed by garbage
law dmw_left_over:
  for +x: Dm.In
  for c: Char
  for rest: String
  for h: {dmw_in_fits(x) == True{} : Bool}
  {FDm.ffi(FDm.put_in(x, SCon{c, rest})) == Wr.err("default_model: input left over") : String}

# LAW R1 anchor: the reasons' tags (0 not in the catalog | 1 no
# credentials | 2 not in the scope)
# EXCLUDES: tags in another order than the grammar's
law dmw_reason_example:
  {FDm.put_reason(Dm.NotInCatalog{}, FDm.put_reason(Dm.NoCredentials{}, FDm.put_reason(Dm.NotInScope{}, ""))) == "0,1,2," : String}

# LAW R1 anchor and witness: a saved default is 0 (none) or 1, then it
# EXCLUDES: a vacuous dmw_saved_round_trip, another spelling
law dmw_saved_example:
  {dmw_saved_fits(Dm.Default{5n}) == True{} : Bool} & {FDm.put_saved(Dm.NoDefault{}, FDm.put_saved(Dm.Default{5n}, "")) == "0,1,5," : String}

# LAW R1 anchor and witness: the chain's pick is 0 (none) or 1, then it
# EXCLUDES: a vacuous dmw_next_round_trip, another spelling
law dmw_next_example:
  {dmw_next_fits(Dm.Next{9n}) == True{} : Bool} & {FDm.put_next(Dm.NoNext{}, FDm.put_next(Dm.Next{9n}, "")) == "0,1,9," : String}

# LAW R1 anchor and witness: a request is saved, cat, key, out, next
# EXCLUDES: a vacuous dmw_in_round_trip or dmw_answers, facts in another
#   order
law dmw_in_example:
  {dmw_in_fits(Dm.In{Dm.Default{5n}, True{}, True{}, False{}, Dm.Next{9n}}) == True{} : Bool} & {FDm.put_in(Dm.In{Dm.Default{5n}, True{}, True{}, False{}, Dm.Next{9n}}, "") == "1,5,TTF1,9," : String}

# LAW R1 anchor and witness: a key is the model, then the reason
# EXCLUDES: a vacuous dmw_key_round_trip, fields in another order
law dmw_key_example:
  {dmw_key_fits(Dm.K{5n, Dm.NoCredentials{}}) == True{} : Bool} & {FDm.put_key(Dm.K{5n, Dm.NoCredentials{}}, "") == "5,1," : String}

# LAW R1 anchor and witness: a pick is 0 (the saved default) or 1, then
# the other model
# EXCLUDES: a vacuous dmw_pick_round_trip, tags swapped
law dmw_pick_example:
  {dmw_pick_fits(Dm.Other{3n}) == True{} : Bool} & {FDm.put_pick(Dm.Saved{}, FDm.put_pick(Dm.Other{3n}, "")) == "0,1,3," : String}

# LAW R1 anchor and witness: a substitution is 0 (kept) or 1, then a key
# EXCLUDES: a vacuous dmw_sub_round_trip, tags swapped
law dmw_sub_example:
  {dmw_sub_fits(Dm.Swapped{Dm.K{5n, Dm.NotInCatalog{}}}) == True{} : Bool} & {FDm.put_sub(Dm.Kept{}, FDm.put_sub(Dm.Swapped{Dm.K{5n, Dm.NotInCatalog{}}}, "")) == "0,1,5,0," : String}

# LAW R1 anchor and witness: a reply is 0 pick sub (runs) | 1 (no model) |
# 2 key (refused)
# EXCLUDES: a vacuous dmw_res_round_trip, tags in another order
law dmw_res_example:
  {dmw_res_fits(Dm.Runs{Dm.Other{3n}, Dm.Swapped{Dm.K{5n, Dm.NotInScope{}}}}) == True{} : Bool} & {FDm.put_res(Dm.Runs{Dm.Other{3n}, Dm.Swapped{Dm.K{5n, Dm.NotInScope{}}}}, FDm.put_res(Dm.Nothing{}, FDm.put_res(Dm.Refused{Dm.K{5n, Dm.NoCredentials{}}}, ""))) == "0,1,3,1,5,2,1,2,5,1," : String}

# LAW R2 anchor: a usable saved default runs, end to end
# EXCLUDES: an entry that answers other bytes than the grammar's
law dmw_ffi_example:
  {FDm.ffi("1,5,TTF1,9,") == "0,0,0," : String}

# LAW R3 witness: a saved default with an unknown tag is malformed
# EXCLUDES: a vacuous dmw_malformed
law dmw_malformed_example:
  {FDm.get_in("2,") == Wr.Bad{} : Wr.Dec<Dm.In>} & {FDm.ffi("2,") == Wr.err("default_model: malformed request") : String}

# ---- workflow ----

# LAWS (WF, dynamic workflows): a run never holds more agents at once
# than its concurrency, never spawns more than its budget, spawns only
# the uncached keys when it resumes, and one failed agent never changes
# its siblings' results. An `agent()` call is admitted by one rule
# (W.admit, the Rust `admit` of globals.rs): a call whose ordinal the run
# admitted before never spawns again, a call the earlier run answered
# reuses the first such answer, and only then the budget decides. A run's
# concurrency is its size's, at most the subagent cap (W.effective, the
# Rust `effective_limits`). Each law is an open claim about the model in
# bend/workflow.bend; PROOF.bend proves them (as Laws.<law>) with the
# lemmas of PROOF.bend section workflow.

# Spec helpers
# ------------

# a row status that holds a finished answer: done, or served from cache
def wf_serves(s: W.Sts) -> Bool:
  match s:
    case W.Queued{}:
      False{}
    case W.Running{}:
      False{}
    case W.Finished{}:
      True{}
    case W.Erred{}:
      False{}
    case W.Cancelled{}:
      False{}
    case W.Cached{}:
      True{}

# what a repeated ordinal does: an ended row replays its answer, a
# queued or running one is reattached
def wf_again(s: W.Sts) -> W.Admit:
  match s:
    case W.Queued{}:
      W.Reattach{}
    case W.Running{}:
      W.Reattach{}
    case W.Finished{}:
      W.Ended{}
    case W.Erred{}:
      W.Ended{}
    case W.Cancelled{}:
      W.Ended{}
    case W.Cached{}:
      W.Ended{}

def wf_next(m: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match m:
    case None{}:
      None{}
    case Some{i}:
      Some{1n+i}

def wf_first.at(hit: Bool, rest: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match hit:
    case True{}:
      Some{0n}
    case False{}:
      wf_next(rest)

# the position of the first row of rs with key k and a finished answer
def wf_first(rs: List<&2, W.Row>, +k: Nat) -> Maybe<&2, Nat>:
  match rs:
    case Nil{}:
      None{}
    case W.Row{key, s} <> rest:
      wf_first.at(Bool.and(Nat.is_eq(key, k), wf_serves(s)), wf_first(rest, k))

# the smaller of a and b
def wf_min(a: Nat, b: Nat) -> Nat:
  match a b:
    case 0n _:
      0n
    case 1n+x 0n:
      0n
    case 1n+x 1n+y:
      1n+wf_min(x, y)

# LAW: after any asks and settles, the running agents and the free slots
# still add up to the concurrency: running never goes above it
law wf_running_within_concurrency:
  for cap: Nat
  for es: List<&2, W.Ev>
  {W.size(W.run(es, W.pool(cap))) == cap : Nat}

# LAW: after any number of spawn attempts, the spawned agents and the
# budget left add up to the run's max agents: spawned never goes above it
law wf_spawned_within_budget:
  for max: Nat
  for n: Nat
  {W.size(W.spawns(n, W.pool(max))) == max : Nat}

# LAW: a resumed call whose key the earlier run finished spawns nothing
law wf_cached_key_spawns_nothing:
  for k: Nat
  for cache: List<&2, Nat>
  for hit: {W.member(k, cache) == True{} : Bool}
  {W.cost(k, cache) == 0n : Nat}

# LAW: a resume with nothing cached spawns every key
law wf_empty_cache_spawns_all:
  for keys: List<&2, Nat>
  {W.resumed([], keys) == List.length(&2, Nat, keys) : Nat}

# LAW: a failed agent gives null in its own slot and leaves every
# sibling's result as it was
law wf_failure_spares_siblings:
  for xs: List<&2, W.Out>
  for ys: List<&2, W.Out>
  {W.results(W.cat(xs, W.Failed{} <> ys)) == W.rcat(W.results(xs), None{} <> W.results(ys)) : List<&2, Maybe<&2, Nat>>}

# LAW: a call whose ordinal the run admitted before (a replay after a
# restart) spawns nothing and takes no budget: an ended row replays its
# answer, a queued or running one is reattached
# EXCLUDES: a second agent for one ordinal, budget charged twice, a
#   running agent reported as ended or an ended one run again
law wf_admitted_never_respawns:
  for s: W.Sts
  for k: Nat
  for rs: List<&2, W.Row>
  for p: W.Pool
  {W.admit(Some{s}, k, rs, p) == (wf_again(s), p) : W.Admit & W.Pool}

# LAW: a new call whose key the earlier run answered reuses the first row
# with that key and a finished answer, and takes no budget
# EXCLUDES: a cached key spawned again, a failed or unfinished row
#   reused, a later duplicate reused instead of the first
law wf_reuses_first_answer:
  for +k: Nat
  for +rs: List<&2, W.Row>
  for p: W.Pool
  for i: Nat
  for hit: {wf_first(rs, k) == Some{i} : Maybe<&2, Nat>}
  {W.admit(None{}, k, rs, p) == (W.Reuse{i}, p) : W.Admit & W.Pool}

# LAW: a new call with no earlier answer spawns while the budget has an
# agent left, and takes one agent of it
# EXCLUDES: refusing a call the budget allows, a spawn that takes no budget
law wf_spawns_within_budget:
  for +k: Nat
  for +rs: List<&2, W.Row>
  for t: Nat
  for l: Nat
  for miss: {wf_first(rs, k) == None{} : Maybe<&2, Nat>}
  {W.admit(None{}, k, rs, W.Pool{t, 1n+l}) == (W.Spawn{}, W.Pool{1n+t, l}) : W.Admit & W.Pool}

# LAW: a new call with no earlier answer and no agent left is refused,
# and the budget stays
# EXCLUDES: a spawn past max agents
law wf_refused_when_spent:
  for +k: Nat
  for +rs: List<&2, W.Row>
  for t: Nat
  for miss: {wf_first(rs, k) == None{} : Maybe<&2, Nat>}
  {W.admit(None{}, k, rs, W.Pool{t, 0n}) == (W.Refused{}, W.Pool{t, 0n}) : W.Admit & W.Pool}

# LAW witness: the first answer skips rows of another key and rows
# without a finished answer, and a key with no answer has none
# EXCLUDES: a vacuous wf_reuses_first_answer or wf_spawns_within_budget
law wf_first_example:
  {(wf_first([W.Row{1n, W.Finished{}}, W.Row{2n, W.Running{}}, W.Row{2n, W.Erred{}}, W.Row{2n, W.Cached{}}, W.Row{2n, W.Finished{}}], 2n), wf_first([W.Row{1n, W.Finished{}}], 2n)) == (Some{3n}, None{}) : Maybe<&2, Nat> & Maybe<&2, Nat>}

# LAW: with no subagent cap (0) a run's limits are its size's
# EXCLUDES: a cap of 0 read as "no agents"
law wf_limits_uncapped:
  for c: Nat
  for m: Nat
  {W.effective(W.Limits{c, m}, 0n) == W.Limits{c, m} : W.Limits}

# LAW: under a subagent cap a run's concurrency is the smaller of its
# size's and the cap; its max agents stay
# EXCLUDES: a cap that raises the concurrency, a cap ignored, a cap
#   applied to the max agents
law wf_limits_capped:
  for +c: Nat
  for m: Nat
  for +x: Nat
  {W.effective(W.Limits{c, m}, 1n+x) == W.Limits{wf_min(c, 1n+x), m} : W.Limits}

# The wire codec of bend/ffi_workflow.bend (grammar: that file's header,
# crates/eukhe-bend/WIRE.md). R1: every request and reply reads back; R2:
# a well-formed request answers the model's answer (W.admit, W.effective),
# encoded; R3: a malformed or overlong request answers the error form,
# never a model answer. Every input is free.

# what fits the wire: every Nat (and every list length) at most 14 digits
def wfw_row_fits(r: W.Row) -> Bool:
  match r:
    case W.Row{k, s}:
      wire_fits(k)

def wfw_rows_fit(rs: List<&2, W.Row>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case Con{r, t}:
      Bool.and(wfw_row_fits(r), wfw_rows_fit(t))

def wfw_pool_fits(p: W.Pool) -> Bool:
  match p:
    case W.Pool{t, l}:
      Bool.and(wire_fits(t), wire_fits(l))

def wfw_req_fits(r: FW.Req) -> Bool:
  match r:
    case FW.AdmitReq{prior, k, +rows, p}:
      Bool.and(wire_fits(k), Bool.and(Bool.and(wire_fits(List.length(&2, W.Row, rows)), wfw_rows_fit(rows)), wfw_pool_fits(p)))
    case FW.LimitsReq{c, m, cap}:
      Bool.and(wire_fits(c), Bool.and(wire_fits(m), wire_fits(cap)))

def wfw_admit_fits(a: W.Admit) -> Bool:
  match a:
    case W.Ended{}:
      True{}
    case W.Reattach{}:
      True{}
    case W.Reuse{i}:
      wire_fits(i)
    case W.Spawn{}:
      True{}
    case W.Refused{}:
      True{}

def wfw_limits_fits(l: W.Limits) -> Bool:
  match l:
    case W.Limits{c, m}:
      Bool.and(wire_fits(c), wire_fits(m))

# LAW R1 a row's status reads back, and the rest is untouched
# EXCLUDES: two statuses with one tag, a status read as another
law wfw_sts_round_trip:
  for s: W.Sts
  for rest: String
  {FW.get_sts(FW.put_sts(s, rest)) == Wr.Got{s, rest} : Wr.Dec<W.Sts>}

# LAW R1 the prior row's status (none or one) reads back
# EXCLUDES: a missing prior read as a status, or a status dropped
law wfw_prior_round_trip:
  for m: Maybe<&2, W.Sts>
  for rest: String
  {FW.get_prior(FW.put_prior(m, rest)) == Wr.Got{m, rest} : Wr.Dec<Maybe<&2, W.Sts>>}

# LAW R1 a row that fits reads back
# EXCLUDES: a row's key or status lost or misread
law wfw_row_round_trip:
  for +r: W.Row
  for rest: String
  for h: {wfw_row_fits(r) == True{} : Bool}
  {FW.get_row(FW.put_row(r, rest)) == Wr.Got{r, rest} : Wr.Dec<W.Row>}

# LAW R1 a list of rows that fit, of a length that fits, reads back
# EXCLUDES: rows lost, added, reordered or misread, a wrong count
law wfw_rows_round_trip:
  for +rs: List<&2, W.Row>
  for rest: String
  for h: {Bool.and(wire_fits(List.length(&2, W.Row, rs)), wfw_rows_fit(rs)) == True{} : Bool}
  {Wr.get_list(~W.Row, ~FW.get_row, Wr.put_list(~W.Row, ~FW.put_row, rs, rest)) == Wr.Got{rs, rest} : Wr.Dec<List<&2, W.Row>>}

# LAW R1 a pool that fits reads back (request and reply)
# EXCLUDES: taken and left swapped or misread
law wfw_pool_round_trip:
  for +p: W.Pool
  for rest: String
  for h: {wfw_pool_fits(p) == True{} : Bool}
  {FW.get_pool(FW.put_pool(p, rest)) == Wr.Got{p, rest} : Wr.Dec<W.Pool>}

# LAW R1 a request that fits reads back, of either kind
# EXCLUDES: one kind read as the other, a field lost, swapped or misread
law wfw_req_round_trip:
  for +r: FW.Req
  for rest: String
  for h: {wfw_req_fits(r) == True{} : Bool}
  {FW.get_req(FW.put_req(r, rest)) == Wr.Got{r, rest} : Wr.Dec<FW.Req>}

# LAW R1 an admission decision that fits reads back
# EXCLUDES: two decisions with one tag, a reused row's index misread
law wfw_admit_round_trip:
  for +a: W.Admit
  for rest: String
  for h: {wfw_admit_fits(a) == True{} : Bool}
  {FW.get_admit(FW.put_admit(a, rest)) == Wr.Got{a, rest} : Wr.Dec<W.Admit>}

# LAW R1 the reply to an Admit, the decision then the pool, reads back
# EXCLUDES: a reply that drops the pool or puts it before the decision
law wfw_decision_round_trip:
  for +a: W.Admit
  for +p: W.Pool
  for rest: String
  for h: {Bool.and(wfw_admit_fits(a), wfw_pool_fits(p)) == True{} : Bool}
  {FW.get_decision(FW.put_decision((a, p), rest)) == Wr.Got{(a, p), rest} : Wr.Dec<+Sigma<W.Admit, x => W.Pool>>}

# LAW R1 the reply to a Limits request reads back
# EXCLUDES: concurrency and max agents swapped or misread
law wfw_limits_round_trip:
  for +l: W.Limits
  for rest: String
  for h: {wfw_limits_fits(l) == True{} : Bool}
  {FW.get_limits(FW.put_limits(l, rest)) == Wr.Got{l, rest} : Wr.Dec<W.Limits>}

# LAW R2 an encoded Admit request answers the model's admission, encoded
# EXCLUDES: an entry that decides other than W.admit, or drops a field
#   on the way in or out
law wfw_answers_admit:
  for prior: Maybe<&2, W.Sts>
  for +k: Nat
  for +rows: List<&2, W.Row>
  for p: W.Pool
  for h: {wfw_req_fits(FW.AdmitReq{prior, k, rows, p}) == True{} : Bool}
  {FW.ffi(FW.put_req(FW.AdmitReq{prior, k, rows, p}, "")) == FW.put_decision(W.admit(prior, k, rows, p), "") : String}

# LAW R2 an encoded Limits request answers the model's limits, encoded
# EXCLUDES: an entry that ignores the cap or the run's size
law wfw_answers_limits:
  for +c: Nat
  for +m: Nat
  for +cap: Nat
  for h: {wfw_req_fits(FW.LimitsReq{c, m, cap}) == True{} : Bool}
  {FW.ffi(FW.put_req(FW.LimitsReq{c, m, cap}, "")) == FW.put_limits(W.effective(W.Limits{c, m}, cap), "") : String}

# LAW R3 a malformed request answers the error form
# EXCLUDES: a default answer (a spawn, a limit) for a request it cannot read
law wfw_malformed:
  for +s: String
  for h: {FW.get_req(s) == Wr.Bad{} : Wr.Dec<FW.Req>}
  {FW.ffi(s) == Wr.err("workflow: malformed request") : String}

# LAW R3 a request with input left over answers the error form
# EXCLUDES: an entry that answers a request followed by garbage
law wfw_left_over:
  for +r: FW.Req
  for c: Char
  for rest: String
  for h: {wfw_req_fits(r) == True{} : Bool}
  {FW.ffi(FW.put_req(r, SCon{c, rest})) == Wr.err("workflow: input left over") : String}

# LAW R1 anchor: the tags of the header (Sts 0 queued | 1 running | 2 done
# | 3 failed | 4 cancelled | 5 cached; the decision 0 ended | 1 reattach |
# 2 i reuse | 3 spawn | 4 refused)
# EXCLUDES: tags in another order than the grammar's
law wfw_tags_example:
  {FW.put_sts(W.Queued{}, FW.put_sts(W.Running{}, FW.put_sts(W.Finished{}, FW.put_sts(W.Erred{}, FW.put_sts(W.Cancelled{}, FW.put_sts(W.Cached{}, "")))))) == "0,1,2,3,4,5," : String} & {FW.put_admit(W.Ended{}, FW.put_admit(W.Reattach{}, FW.put_admit(W.Reuse{9n}, FW.put_admit(W.Spawn{}, FW.put_admit(W.Refused{}, ""))))) == "0,1,2,9,3,4," : String}

# LAW R1 anchor: a prior status is 0 (none) or 1, then the status
# EXCLUDES: another spelling of a missing prior row
law wfw_prior_example:
  {FW.put_prior(None{}, FW.put_prior(Some{W.Finished{}}, "")) == "0,1,2," : String}

# LAW R1 anchor and witness: a row is its key, then its status
# EXCLUDES: a vacuous wfw_row_round_trip, fields in another order
law wfw_row_example:
  {wfw_row_fits(W.Row{3n, W.Erred{}}) == True{} : Bool} & {FW.put_row(W.Row{3n, W.Erred{}}, "") == "3,3," : String}

# LAW R1 anchor and witness: rows are their count, then each row
# EXCLUDES: a vacuous wfw_rows_round_trip
law wfw_rows_example:
  {Bool.and(wire_fits(List.length(&2, W.Row, [W.Row{3n, W.Erred{}}, W.Row{4n, W.Cached{}}])), wfw_rows_fit([W.Row{3n, W.Erred{}}, W.Row{4n, W.Cached{}}])) == True{} : Bool} & {Wr.put_list(~W.Row, ~FW.put_row, [W.Row{3n, W.Erred{}}, W.Row{4n, W.Cached{}}], "") == "2,3,3,4,5," : String}

# LAW R1 anchor and witness: a pool is taken, then left
# EXCLUDES: a vacuous wfw_pool_round_trip, fields in another order
law wfw_pool_example:
  {wfw_pool_fits(W.Pool{1n, 2n}) == True{} : Bool} & {FW.put_pool(W.Pool{1n, 2n}, "") == "1,2," : String}

# LAW R1 anchor and witness: an Admit request is 0, prior, key, rows, pool
# EXCLUDES: a vacuous wfw_req_round_trip or wfw_answers_admit, fields in
#   another order
law wfw_admit_req_example:
  {wfw_req_fits(FW.AdmitReq{Some{W.Cached{}}, 7n, [W.Row{3n, W.Erred{}}], W.Pool{1n, 2n}}) == True{} : Bool} & {FW.put_req(FW.AdmitReq{Some{W.Cached{}}, 7n, [W.Row{3n, W.Erred{}}], W.Pool{1n, 2n}}, "") == "0,1,5,7,1,3,3,1,2," : String}

# LAW R1 anchor and witness: a Limits request is 1, concurrency, max
# agents, cap
# EXCLUDES: a vacuous wfw_answers_limits, fields in another order
law wfw_limits_req_example:
  {wfw_req_fits(FW.LimitsReq{4n, 9n, 2n}) == True{} : Bool} & {FW.put_req(FW.LimitsReq{4n, 9n, 2n}, "") == "1,4,9,2," : String}

# LAW R1 anchor and witness: a reused row's decision carries its index
# EXCLUDES: a vacuous wfw_admit_round_trip
law wfw_admit_example:
  {wfw_admit_fits(W.Reuse{2n}) == True{} : Bool} & {FW.put_admit(W.Reuse{2n}, "") == "2,2," : String}

# LAW R1 anchor and witness: the reply to an Admit is the decision, then
# the pool
# EXCLUDES: a vacuous wfw_decision_round_trip
law wfw_decision_example:
  {Bool.and(wfw_admit_fits(W.Reuse{2n}), wfw_pool_fits(W.Pool{1n, 0n})) == True{} : Bool} & {FW.put_decision((W.Reuse{2n}, W.Pool{1n, 0n}), "") == "2,2,1,0," : String}

# LAW R1 anchor and witness: the reply to Limits is concurrency, max agents
# EXCLUDES: a vacuous wfw_limits_round_trip
law wfw_limits_example:
  {wfw_limits_fits(W.Limits{2n, 9n}) == True{} : Bool} & {FW.put_limits(W.Limits{2n, 9n}, "") == "2,9," : String}

# LAW R2 anchor: a run of concurrency 4 and 9 agents capped at 2 runs 2
# at once, 9 agents, end to end
# EXCLUDES: an entry that answers other bytes than the grammar's
law wfw_ffi_example:
  {FW.ffi("1,4,9,2,") == "2,9," : String}

# LAW R3 witness: a request with an unknown kind is malformed
# EXCLUDES: a vacuous wfw_malformed
law wfw_malformed_example:
  {FW.get_req("2,") == Wr.Bad{} : Wr.Dec<FW.Req>} & {FW.ffi("2,") == Wr.err("workflow: malformed request") : String}

# ---- admission_wire ----

# The wire codec of bend/ffi_admission.bend (the stepper of the compiled
# Bend core; grammar: that file's header, crates/eukhe-bend/WIRE.md). R1:
# every value the stepper and Rust exchange reads back; R2: a well-formed
# open or step answers the model's new controller, encoded; R3: a
# malformed or overlong input answers the error form and changes nothing.
# Every input is free: any limits, any op, any controller, any text.

# what fits the wire: every Nat (and every list length) at most 14 digits
def adw_lim_fits(l: Ad.Lim) -> Bool:
  match l:
    case Ad.Unl{}:
      True{}
    case Ad.Cap{p}:
      wire_fits(p)

def adw_lv_fits(t: Ad.Lv) -> Bool:
  match t:
    case Ad.Lv{k, c, s}:
      wire_fits(k)

def adw_lvs_fit(ts: List<&2, Ad.Lv>) -> Bool:
  match ts:
    case Nil{}:
      True{}
    case Con{t, u}:
      Bool.and(adw_lv_fits(t), adw_lvs_fit(u))

def adw_live_fits(x: Ad.Live) -> Bool:
  match x:
    case Ad.Live{l, q, +ts, n}:
      Bool.and(adw_lim_fits(l), Bool.and(wire_fits(q), Bool.and(Bool.and(wire_fits(List.length(&2, Ad.Lv, ts)), adw_lvs_fit(ts)), wire_fits(n))))

def adw_op_fits(o: Ad.Op) -> Bool:
  match o:
    case Ad.Admit{c}:
      True{}
    case Ad.Collect{k}:
      wire_fits(k)
    case Ad.Release{k}:
      wire_fits(k)
    case Ad.Leave{k}:
      wire_fits(k)
    case Ad.Limit{l, q}:
      Bool.and(adw_lim_fits(l), wire_fits(q))

# LAW R1 a ticket's class reads back, and the rest is untouched
# EXCLUDES: swapped class tags, a class that eats the rest
law adw_cls_round_trip:
  for c: Ad.Cls
  for rest: String
  {FAd.get_cls(FAd.put_cls(c, rest)) == Wr.Got{c, rest} : Wr.Dec<Ad.Cls>}

# LAW R1 a ticket's status reads back, and the rest is untouched
# EXCLUDES: two statuses with one tag, a status read as another
law adw_sts_round_trip:
  for s: Ad.Sts
  for rest: String
  {FAd.get_sts(FAd.put_sts(s, rest)) == Wr.Got{s, rest} : Wr.Dec<Ad.Sts>}

# LAW R1 a limit that fits reads back, and the rest is untouched
# EXCLUDES: a cap read as unlimited, a misread slot count
law adw_lim_round_trip:
  for +l: Ad.Lim
  for rest: String
  for h: {adw_lim_fits(l) == True{} : Bool}
  {FAd.get_lim(FAd.put_lim(l, rest)) == Wr.Got{l, rest} : Wr.Dec<Ad.Lim>}

# LAW R1 a live ticket that fits reads back, and the rest is untouched
# EXCLUDES: a ticket's number, class or status lost or misread
law adw_lv_round_trip:
  for +t: Ad.Lv
  for rest: String
  for h: {adw_lv_fits(t) == True{} : Bool}
  {FAd.get_lv(FAd.put_lv(t, rest)) == Wr.Got{t, rest} : Wr.Dec<Ad.Lv>}

# LAW R1 a list of live tickets that fit, of a length that fits, reads back
# EXCLUDES: tickets lost, added, reordered or misread, a wrong count
law adw_lvs_round_trip:
  for +ts: List<&2, Ad.Lv>
  for rest: String
  for h: {Bool.and(wire_fits(List.length(&2, Ad.Lv, ts)), adw_lvs_fit(ts)) == True{} : Bool}
  {Wr.get_list(~Ad.Lv, ~FAd.get_lv, Wr.put_list(~Ad.Lv, ~FAd.put_lv, ts, rest)) == Wr.Got{ts, rest} : Wr.Dec<List<&2, Ad.Lv>>}

# LAW R1 the reply, a controller that fits, reads back
# EXCLUDES: a reply that drops or misreads the limits, a ticket or the
#   next ticket's number
law adw_live_round_trip:
  for +x: Ad.Live
  for rest: String
  for h: {adw_live_fits(x) == True{} : Bool}
  {FAd.get_live(FAd.put_live(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Ad.Live>}

# LAW R1 the request of a step, an op that fits, reads back
# EXCLUDES: one op read as another, a misread ticket number or limit
law adw_op_round_trip:
  for +o: Ad.Op
  for rest: String
  for h: {adw_op_fits(o) == True{} : Bool}
  {FAd.get_op(FAd.put_op(o, rest)) == Wr.Got{o, rest} : Wr.Dec<Ad.Op>}

# LAW R1 the request of an open, limits that fit, reads back
# EXCLUDES: the limit and providerMaxQueued swapped or misread
law adw_open_round_trip:
  for +l: Ad.Lim
  for +q: Nat
  for rest: String
  for h: {Bool.and(adw_lim_fits(l), wire_fits(q)) == True{} : Bool}
  {FAd.get_open(FAd.put_lim(l, Wr.put_nat(q, rest))) == Wr.Got{(l, q), rest} : Wr.Dec<+Sigma<Ad.Lim, x => Nat>>}

# LAW R2 an encoded open runs the model's open: the new controller, and
# its encoding as the reply
# EXCLUDES: an open that ignores or misreads its limits, a reply that is
#   not the state kept
law adw_open_answers:
  for +l: Ad.Lim
  for +q: Nat
  for h: {Bool.and(adw_lim_fits(l), wire_fits(q)) == True{} : Bool}
  {FAd.open(FAd.put_lim(l, Wr.put_nat(q, ""))) == (FAd.Running{Ad.Live.new(l, q)}, FAd.put_live(Ad.Live.new(l, q), "")) : FAd.St & String}

# LAW R2 an encoded op runs the model's step on the kept controller: the
# new controller, and its encoding as the reply
# EXCLUDES: a step that drops or reorders ops, a state that drifts from
#   the model, a reply that is not the state kept
law adw_step_answers:
  for +x: Ad.Live
  for +o: Ad.Op
  for h: {adw_op_fits(o) == True{} : Bool}
  {FAd.step(FAd.Running{x}, FAd.put_op(o, "")) == (FAd.Running{Ad.Live.step(x, o)}, FAd.put_live(Ad.Live.step(x, o), "")) : FAd.St & String}

# LAW R3 a malformed open opens the refused state, with the error form
# EXCLUDES: a default controller for malformed limits
law adw_open_malformed:
  for +s: String
  for h: {FAd.get_open(s) == Wr.Bad{} : Wr.Dec<+Sigma<Ad.Lim, x => Nat>>}
  {FAd.open(s) == (FAd.Shut{}, Wr.err("admission: malformed open")) : FAd.St & String}

# LAW R3 an open with input left over is refused too
# EXCLUDES: an open that ignores trailing input
law adw_open_left_over:
  for +l: Ad.Lim
  for +q: Nat
  for c: Char
  for rest: String
  for h: {Bool.and(adw_lim_fits(l), wire_fits(q)) == True{} : Bool}
  {FAd.open(FAd.put_lim(l, Wr.put_nat(q, SCon{c, rest}))) == (FAd.Shut{}, Wr.err("admission: input left over")) : FAd.St & String}

# LAW R3 a malformed op answers the error form and keeps the controller
# EXCLUDES: a guessed op, a controller lost or changed by a bad input
law adw_step_malformed:
  for x: Ad.Live
  for +s: String
  for h: {FAd.get_op(s) == Wr.Bad{} : Wr.Dec<Ad.Op>}
  {FAd.step(FAd.Running{x}, s) == (FAd.Running{x}, Wr.err("admission: malformed op")) : FAd.St & String}

# LAW R3 an op with input left over answers the error form and keeps the
# controller
# EXCLUDES: a step that runs an op followed by garbage
law adw_step_left_over:
  for x: Ad.Live
  for +o: Ad.Op
  for c: Char
  for rest: String
  for h: {adw_op_fits(o) == True{} : Bool}
  {FAd.step(FAd.Running{x}, FAd.put_op(o, SCon{c, rest})) == (FAd.Running{x}, Wr.err("admission: input left over")) : FAd.St & String}

# LAW R3 the refused state answers every step with the error form
# EXCLUDES: a refused open that later runs ops on a made-up controller
law adw_shut_refuses:
  for s: String
  {FAd.step(FAd.Shut{}, s) == (FAd.Shut{}, Wr.err("admission: the open was refused")) : FAd.St & String}

# LAW R1 anchor: the tags of the header (Cls 0 interactive | 1 background;
# Sts 0 queued | 1 granted | 2 held | 3 preempted | 4 ended)
# EXCLUDES: tags in another order than the grammar's
law adw_tags_example:
  {FAd.put_cls(Ad.Ia{}, FAd.put_cls(Ad.Bg{}, "")) == "0,1," : String} & {FAd.put_sts(Ad.Queued{}, FAd.put_sts(Ad.Granted{}, FAd.put_sts(Ad.Held{}, FAd.put_sts(Ad.Preempted{}, FAd.put_sts(Ad.Ended{}, ""))))) == "0,1,2,3,4," : String}

# LAW R1 anchor and witness: a cap of 1 + 2 slots is 1, 2
# EXCLUDES: a vacuous adw_lim_round_trip, a cap spelled otherwise
law adw_lim_example:
  {adw_lim_fits(Ad.Cap{2n}) == True{} : Bool} & {FAd.put_lim(Ad.Cap{2n}, FAd.put_lim(Ad.Unl{}, "")) == "1,2,0," : String}

# LAW R1 anchor and witness: a live ticket is its number, class, status
# EXCLUDES: a vacuous adw_lv_round_trip, fields in another order
law adw_lv_example:
  {adw_lv_fits(Ad.Lv{3n, Ad.Bg{}, Ad.Preempted{}}) == True{} : Bool} & {FAd.put_lv(Ad.Lv{3n, Ad.Bg{}, Ad.Preempted{}}, "") == "3,1,3," : String}

# LAW R1 anchor and witness: a list of tickets is its count, then them
# EXCLUDES: a vacuous adw_lvs_round_trip
law adw_lvs_example:
  {Bool.and(wire_fits(List.length(&2, Ad.Lv, [Ad.Lv{0n, Ad.Ia{}, Ad.Queued{}}, Ad.Lv{1n, Ad.Bg{}, Ad.Ended{}}])), adw_lvs_fit([Ad.Lv{0n, Ad.Ia{}, Ad.Queued{}}, Ad.Lv{1n, Ad.Bg{}, Ad.Ended{}}])) == True{} : Bool} & {Wr.put_list(~Ad.Lv, ~FAd.put_lv, [Ad.Lv{0n, Ad.Ia{}, Ad.Queued{}}, Ad.Lv{1n, Ad.Bg{}, Ad.Ended{}}], "") == "2,0,0,0,1,1,4," : String}

# LAW R1 anchor and witness: a controller is its limit, providerMaxQueued,
# live tickets and next ticket's number
# EXCLUDES: a vacuous adw_live_round_trip, fields in another order
law adw_live_example:
  {adw_live_fits(Ad.Live{Ad.Cap{0n}, 1n, [Ad.Lv{1n, Ad.Ia{}, Ad.Granted{}}], 2n}) == True{} : Bool} & {FAd.put_live(Ad.Live{Ad.Cap{0n}, 1n, [Ad.Lv{1n, Ad.Ia{}, Ad.Granted{}}], 2n}, "") == "1,0,1,1,1,0,1,2," : String}

# LAW R1 anchor and witness: every op's tag and fields
# EXCLUDES: a vacuous adw_op_round_trip, op tags in another order
law adw_op_example:
  {adw_op_fits(Ad.Limit{Ad.Cap{2n}, 3n}) == True{} : Bool} & {FAd.put_op(Ad.Admit{Ad.Bg{}}, FAd.put_op(Ad.Collect{5n}, FAd.put_op(Ad.Release{6n}, FAd.put_op(Ad.Leave{7n}, FAd.put_op(Ad.Limit{Ad.Cap{2n}, 3n}, ""))))) == "0,1,1,5,2,6,3,7,4,1,2,3," : String}

# LAW R2 anchor and witness: open on 0, 3 (unlimited, 3 queued) answers
# the controller with no ticket
# EXCLUDES: a vacuous adw_open_answers, an open that grants or numbers
#   tickets before any op
law adw_open_example:
  {Bool.and(adw_lim_fits(Ad.Unl{}), wire_fits(3n)) == True{} : Bool} & {FAd.open("0,3,") == (FAd.Running{Ad.Live{Ad.Unl{}, 3n, Nil{}, 0n}}, "0,3,0,0,") : FAd.St & String}

# LAW R3 witness: malformed inputs exist (an unknown limit tag, an
# unknown op tag)
# EXCLUDES: a vacuous adw_open_malformed or adw_step_malformed
law adw_malformed_example:
  {FAd.get_open("2,0,") == Wr.Bad{} : Wr.Dec<+Sigma<Ad.Lim, x => Nat>>} & {FAd.get_op("5,") == Wr.Bad{} : Wr.Dec<Ad.Op>}

# ---- aux_fallback_wire ----

# The wire codec of bend/ffi_aux_fallback.bend (grammar: that file's
# header, crates/eukhe-bend/WIRE.md). R1: every request and reply reads
# back; R2: a well-formed request answers the model's answer (Af.gate,
# Af.settle, Af.put and Af.after), encoded; R3: a malformed or overlong
# request answers the error form, never a route. Every input is free.

# what fits the wire: every Nat (and every list length) at most 14 digits
def afw_key_fits(k: Af.Key) -> Bool:
  match k:
    case Af.K{p, s, r}:
      Bool.and(wire_fits(p), Bool.and(wire_fits(s), wire_fits(r)))

def afw_keys_fit(ks: List<&2, Af.Key>) -> Bool:
  match ks:
    case Nil{}:
      True{}
    case Con{k, t}:
      Bool.and(afw_key_fits(k), afw_keys_fit(t))

def afw_route_fits(r: Af.Route) -> Bool:
  match r:
    case Af.Session{}:
      True{}
    case Af.Routed{}:
      True{}
    case Af.Fallback{k}:
      afw_key_fits(k)

def afw_gate_fits(g: Af.Gate) -> Bool:
  match g:
    case Af.Known{r}:
      afw_route_fits(r)
    case Af.Lookup{p, s}:
      Bool.and(wire_fits(p), wire_fits(s))

def afw_sel_fits(x: Af.Sel) -> Bool:
  match x:
    case Af.Unset{}:
      True{}
    case Af.Same{}:
      True{}
    case Af.Other{s}:
      wire_fits(s)

def afw_look_fits(x: Af.Look) -> Bool:
  match x:
    case Af.Miss{r}:
      wire_fits(r)
    case Af.Hit{w}:
      wire_fits(w)

def afw_ev_fits(e: Af.Ev) -> Bool:
  match e:
    case Af.Stay{}:
      True{}
    case Af.Went{}:
      True{}
    case Af.Sub{k}:
      afw_key_fits(k)
    case Af.Note{k}:
      afw_key_fits(k)

def afw_evs_fit(es: List<&2, Af.Ev>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case Con{e, t}:
      Bool.and(afw_ev_fits(e), afw_evs_fit(t))

def afw_req_fits(x: FAf.Req) -> Bool:
  match x:
    case FAf.GateReq{p, sel, ok}:
      Bool.and(wire_fits(p), afw_sel_fits(sel))
    case FAf.SettleReq{g, look, need}:
      Bool.and(afw_gate_fits(g), Bool.and(afw_look_fits(look), wire_fits(need)))
    case FAf.PassReq{r, +sh}:
      Bool.and(afw_route_fits(r), Bool.and(wire_fits(List.length(&2, Af.Key, sh)), afw_keys_fit(sh)))

# the reply to a pass fits: both lists and their lengths
def afw_pass_fits(+es: List<&2, Af.Ev>, +ks: List<&2, Af.Key>) -> Bool:
  Bool.and(Bool.and(wire_fits(List.length(&2, Af.Ev, es)), afw_evs_fit(es)), Bool.and(wire_fits(List.length(&2, Af.Key, ks)), afw_keys_fit(ks)))

# LAW R1 a fallback's key that fits reads back
# EXCLUDES: purpose, selector or reason lost, swapped or misread
law afw_key_round_trip:
  for +k: Af.Key
  for rest: String
  for h: {afw_key_fits(k) == True{} : Bool}
  {FAf.get_key(FAf.put_key(k, rest)) == Wr.Got{k, rest} : Wr.Dec<Af.Key>}

# LAW R1 a list of keys that fit, of a length that fits, reads back
# EXCLUDES: shown keys lost, added, reordered or misread, a wrong count
law afw_keys_round_trip:
  for +ks: List<&2, Af.Key>
  for rest: String
  for h: {Bool.and(wire_fits(List.length(&2, Af.Key, ks)), afw_keys_fit(ks)) == True{} : Bool}
  {Wr.get_list(~Af.Key, ~FAf.get_key, Wr.put_list(~Af.Key, ~FAf.put_key, ks, rest)) == Wr.Got{ks, rest} : Wr.Dec<List<&2, Af.Key>>}

# LAW R1 a route that fits reads back (request and reply)
# EXCLUDES: one route read as another, a fallback's key misread
law afw_route_round_trip:
  for +r: Af.Route
  for rest: String
  for h: {afw_route_fits(r) == True{} : Bool}
  {FAf.get_route(FAf.put_route(r, rest)) == Wr.Got{r, rest} : Wr.Dec<Af.Route>}

# LAW R1 a gate's answer that fits reads back (request and reply)
# EXCLUDES: a decided route read as a lookup, or the reverse
law afw_gate_round_trip:
  for +g: Af.Gate
  for rest: String
  for h: {afw_gate_fits(g) == True{} : Bool}
  {FAf.get_gate(FAf.put_gate(g, rest)) == Wr.Got{g, rest} : Wr.Dec<Af.Gate>}

# LAW R1 a selector that fits reads back
# EXCLUDES: unset read as the session model, a misread selector
law afw_sel_round_trip:
  for +x: Af.Sel
  for rest: String
  for h: {afw_sel_fits(x) == True{} : Bool}
  {FAf.get_sel(FAf.put_sel(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Af.Sel>}

# LAW R1 a lookup's result that fits reads back
# EXCLUDES: a miss read as a hit, or the reverse; a misread window
law afw_look_round_trip:
  for +x: Af.Look
  for rest: String
  for h: {afw_look_fits(x) == True{} : Bool}
  {FAf.get_look(FAf.put_look(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Af.Look>}

# LAW R1 an event that fits reads back
# EXCLUDES: a substitution read as a notice, or the reverse
law afw_ev_round_trip:
  for +e: Af.Ev
  for rest: String
  for h: {afw_ev_fits(e) == True{} : Bool}
  {FAf.get_ev(FAf.put_ev(e, rest)) == Wr.Got{e, rest} : Wr.Dec<Af.Ev>}

# LAW R1 a list of events that fit, of a length that fits, reads back
# EXCLUDES: events lost, added, reordered or misread, a wrong count
law afw_evs_round_trip:
  for +es: List<&2, Af.Ev>
  for rest: String
  for h: {Bool.and(wire_fits(List.length(&2, Af.Ev, es)), afw_evs_fit(es)) == True{} : Bool}
  {Wr.get_list(~Af.Ev, ~FAf.get_ev, Wr.put_list(~Af.Ev, ~FAf.put_ev, es, rest)) == Wr.Got{es, rest} : Wr.Dec<List<&2, Af.Ev>>}

# LAW R1 a request that fits reads back, of every kind
# EXCLUDES: one kind read as another, a field lost, swapped or misread
law afw_req_round_trip:
  for +x: FAf.Req
  for rest: String
  for h: {afw_req_fits(x) == True{} : Bool}
  {FAf.get_req(FAf.put_req(x, rest)) == Wr.Got{x, rest} : Wr.Dec<FAf.Req>}

# LAW R1 the reply to a pass, its events then the shown keys, reads back
# EXCLUDES: the two lists swapped, merged or cut
law afw_pass_round_trip:
  for +es: List<&2, Af.Ev>
  for +ks: List<&2, Af.Key>
  for rest: String
  for h: {afw_pass_fits(es, ks) == True{} : Bool}
  {FAf.get_pass(FAf.put_pass((es, ks), rest)) == Wr.Got{(es, ks), rest} : Wr.Dec<+Sigma<List<&2, Af.Ev>, x => List<&2, Af.Key>>>}

# LAW R2 an encoded Gate request answers the model's gate, encoded
# EXCLUDES: an entry that gates other than Af.gate, or drops a field
law afw_answers_gate:
  for +p: Nat
  for +sel: Af.Sel
  for +ok: Bool
  for h: {afw_req_fits(FAf.GateReq{p, sel, ok}) == True{} : Bool}
  {FAf.ffi(FAf.put_req(FAf.GateReq{p, sel, ok}, "")) == FAf.put_gate(Af.gate(p, sel, ok), "") : String}

# LAW R2 an encoded Settle request answers the model's route, encoded
# EXCLUDES: an entry that settles other than Af.settle, or drops a field
law afw_answers_settle:
  for +g: Af.Gate
  for +look: Af.Look
  for +need: Nat
  for h: {afw_req_fits(FAf.SettleReq{g, look, need}) == True{} : Bool}
  {FAf.ffi(FAf.put_req(FAf.SettleReq{g, look, need}, "")) == FAf.put_route(Af.settle(g, look, need), "") : String}

# LAW R2 an encoded Pass request answers the model's events and shown
# keys, encoded
# EXCLUDES: a notice shown twice or lost on the way out, the shown keys
#   of another route
law afw_answers_pass:
  for +r: Af.Route
  for +sh: List<&2, Af.Key>
  for h: {afw_req_fits(FAf.PassReq{r, sh}) == True{} : Bool}
  {FAf.ffi(FAf.put_req(FAf.PassReq{r, sh}, "")) == FAf.put_pass((Af.put(r, sh, Nil{}), Af.after(r, sh)), "") : String}

# LAW R3 a malformed request answers the error form
# EXCLUDES: a default route for a request it cannot read
law afw_malformed:
  for +s: String
  for h: {FAf.get_req(s) == Wr.Bad{} : Wr.Dec<FAf.Req>}
  {FAf.ffi(s) == Wr.err("aux_fallback: malformed request") : String}

# LAW R3 a request with input left over answers the error form
# EXCLUDES: an entry that answers a request followed by garbage
law afw_left_over:
  for +x: FAf.Req
  for c: Char
  for rest: String
  for h: {afw_req_fits(x) == True{} : Bool}
  {FAf.ffi(FAf.put_req(x, SCon{c, rest})) == Wr.err("aux_fallback: input left over") : String}

# LAW R1 anchor and witness: a key is purpose, selector, reason
# EXCLUDES: a vacuous afw_key_round_trip, fields in another order
law afw_key_example:
  {afw_key_fits(Af.K{1n, 2n, 3n}) == True{} : Bool} & {FAf.put_key(Af.K{1n, 2n, 3n}, "") == "1,2,3," : String}

# LAW R1 anchor and witness: keys are their count, then each key
# EXCLUDES: a vacuous afw_keys_round_trip
law afw_keys_example:
  {Bool.and(wire_fits(List.length(&2, Af.Key, [Af.K{1n, 2n, 3n}])), afw_keys_fit([Af.K{1n, 2n, 3n}])) == True{} : Bool} & {Wr.put_list(~Af.Key, ~FAf.put_key, [Af.K{1n, 2n, 3n}], "") == "1,1,2,3," : String}

# LAW R1 anchor and witness: a route is 0 session | 1 routed | 2 key
# EXCLUDES: a vacuous afw_route_round_trip, tags in another order
law afw_route_example:
  {afw_route_fits(Af.Fallback{Af.K{1n, 2n, 3n}}) == True{} : Bool} & {FAf.put_route(Af.Session{}, FAf.put_route(Af.Routed{}, FAf.put_route(Af.Fallback{Af.K{1n, 2n, 3n}}, ""))) == "0,1,2,1,2,3," : String}

# LAW R1 anchor and witness: a gate's answer is 0 route | 1 p s
# EXCLUDES: a vacuous afw_gate_round_trip, tags swapped
law afw_gate_example:
  {afw_gate_fits(Af.Lookup{3n, 8n}) == True{} : Bool} & {FAf.put_gate(Af.Known{Af.Routed{}}, FAf.put_gate(Af.Lookup{3n, 8n}, "")) == "0,1,1,3,8," : String}

# LAW R1 anchor and witness: a selector is 0 unset | 1 session | 2 s
# EXCLUDES: a vacuous afw_sel_round_trip, tags in another order
law afw_sel_example:
  {afw_sel_fits(Af.Other{8n}) == True{} : Bool} & {FAf.put_sel(Af.Unset{}, FAf.put_sel(Af.Same{}, FAf.put_sel(Af.Other{8n}, ""))) == "0,1,2,8," : String}

# LAW R1 anchor and witness: a lookup is 0 r (nothing usable) | 1 w (found)
# EXCLUDES: a vacuous afw_look_round_trip, tags swapped
law afw_look_example:
  {afw_look_fits(Af.Hit{10n}) == True{} : Bool} & {FAf.put_look(Af.Miss{4n}, FAf.put_look(Af.Hit{10n}, "")) == "0,4,1,10," : String}

# LAW R1 anchor and witness: an event is 0 stay | 1 went | 2 key | 3 key
# EXCLUDES: a vacuous afw_ev_round_trip, tags in another order
law afw_ev_example:
  {afw_ev_fits(Af.Note{Af.K{1n, 2n, 3n}}) == True{} : Bool} & {FAf.put_ev(Af.Stay{}, FAf.put_ev(Af.Went{}, FAf.put_ev(Af.Sub{Af.K{1n, 2n, 3n}}, FAf.put_ev(Af.Note{Af.K{4n, 5n, 6n}}, "")))) == "0,1,2,1,2,3,3,4,5,6," : String}

# LAW R1 anchor and witness: events are their count, then each event
# EXCLUDES: a vacuous afw_evs_round_trip
law afw_evs_example:
  {Bool.and(wire_fits(List.length(&2, Af.Ev, [Af.Stay{}, Af.Sub{Af.K{1n, 2n, 3n}}])), afw_evs_fit([Af.Stay{}, Af.Sub{Af.K{1n, 2n, 3n}}])) == True{} : Bool} & {Wr.put_list(~Af.Ev, ~FAf.put_ev, [Af.Stay{}, Af.Sub{Af.K{1n, 2n, 3n}}], "") == "2,0,2,1,2,3," : String}

# LAW R1 anchor and witness: a Gate request is 0, p, Sel, ok
# EXCLUDES: a vacuous afw_answers_gate, fields in another order
law afw_gate_req_example:
  {afw_req_fits(FAf.GateReq{3n, Af.Other{8n}, True{}}) == True{} : Bool} & {FAf.put_req(FAf.GateReq{3n, Af.Other{8n}, True{}}, "") == "0,3,2,8,T" : String}

# LAW R1 anchor and witness: a Settle request is 1, GateR, Look, need
# EXCLUDES: a vacuous afw_answers_settle, fields in another order
law afw_settle_req_example:
  {afw_req_fits(FAf.SettleReq{Af.Lookup{3n, 8n}, Af.Hit{10n}, 5n}) == True{} : Bool} & {FAf.put_req(FAf.SettleReq{Af.Lookup{3n, 8n}, Af.Hit{10n}, 5n}, "") == "1,1,3,8,1,10,5," : String}

# LAW R1 anchor and witness: a Pass request is 2, Route, shown keys
# EXCLUDES: a vacuous afw_answers_pass, fields in another order
law afw_pass_req_example:
  {afw_req_fits(FAf.PassReq{Af.Fallback{Af.K{1n, 2n, 3n}}, [Af.K{1n, 2n, 3n}]}) == True{} : Bool} & {FAf.put_req(FAf.PassReq{Af.Fallback{Af.K{1n, 2n, 3n}}, [Af.K{1n, 2n, 3n}]}, "") == "2,2,1,2,3,1,1,2,3," : String}

# LAW R1 anchor and witness: a pass's reply is its events, then its keys
# EXCLUDES: a vacuous afw_pass_round_trip, the lists swapped
law afw_pass_example:
  {afw_pass_fits([Af.Stay{}], [Af.K{1n, 2n, 3n}]) == True{} : Bool} & {FAf.put_pass(([Af.Stay{}], [Af.K{1n, 2n, 3n}]), "") == "1,0,1,1,2,3," : String}

# LAW R2 anchor: a fallback pass with no key shown substitutes and shows
# its notice, end to end
# EXCLUDES: an entry that answers other bytes than the grammar's
law afw_ffi_example:
  {FAf.ffi("2,2,1,2,3,0,") == "2,2,1,2,3,3,1,2,3,1,1,2,3," : String}

# LAW R3 witness: a request of an unknown kind is malformed
# EXCLUDES: a vacuous afw_malformed
law afw_malformed_example:
  {FAf.get_req("3,") == Wr.Bad{} : Wr.Dec<FAf.Req>} & {FAf.ffi("3,") == Wr.err("aux_fallback: malformed request") : String}

# ---- core_w6 ----

# LAWS: the entries of the compiled Bend core for the child task, the jobs,
# the goal's progress check and the hand-back (bend/ffi_child.bend,
# bend/ffi_job.bend, bend/ffi_progress.bend, bend/ffi_sandbox.bend). Each
# entry, on the request Rust writes (`put_req`, every number within the
# wire), answers the encoding of the model's decision: the codec loses,
# invents and reorders nothing, and the Rust rule is the proven model.

# a content id or a token that fits the wire (None always does)
def wire_mfits(m: Maybe<&2, Nat>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{x}:
      wire_fits(x)

def wire_cfg_fits(c: Ch.Cfg) -> Bool:
  match c:
    case Ch.Cfg{s, f}:
      Bool.and(wire_fits(s), wire_fits(f))

def wire_w_fits(w: Ch.W) -> Bool:
  match w:
    case Ch.W{t, l, n}:
      Bool.and(wire_mfits(t), Bool.and(wire_fits(l), wire_fits(n)))

def wire_obs_fits(o: Ch.Obs) -> Bool:
  match o:
    case Ch.Busy{t}:
      wire_mfits(t)
    case Ch.Lost{}:
      True{}
    case Ch.Answered{r}:
      True{}
    case Ch.Broke{}:
      True{}
    case Ch.Gone{}:
      True{}

def wire_ph_fits(p: Ch.Ph) -> Bool:
  match p:
    case Ch.Watching{w}:
      wire_w_fits(w)
    case Ch.Owing{k, n}:
      wire_fits(n)
    case Ch.Ended{}:
      True{}

def wire_job_fits(j: Jb.J) -> Bool:
  match j:
    case Jb.Live{k, d}:
      Bool.and(wire_fits(k), wire_fits(d))
    case Jb.Ended{k, d, e}:
      Bool.and(wire_fits(k), wire_fits(d))

def wire_ev_fits(e: Jb.JEv) -> Bool:
  match e:
    case Jb.Out{n}:
      wire_fits(n)
    case Jb.Quit{c}:
      True{}
    case Jb.Kill{}:
      True{}
    case Jb.Tick{}:
      True{}

def wire_prior_fits(p: Maybe<&2, Pr.Prior>) -> Bool:
  match p:
    case None{}:
      True{}
    case Some{x}:
      match x:
        case Pr.Prior{s, w}:
          Bool.and(wire_fits(s), wire_fits(w))

# LAW: the child entry's verdict request answers the task's call
# EXCLUDES: a codec that drops or swaps a field, a default for a field
law child_entry_verdict:
  for +c: Ch.Cfg
  for +w: Ch.W
  for +e: Nat
  for +o: Ch.Obs
  for +m: Ch.Mode
  for hc: {wire_cfg_fits(c) == True{} : Bool}
  for hw: {wire_w_fits(w) == True{} : Bool}
  for he: {wire_fits(e) == True{} : Bool}
  for ho: {wire_obs_fits(o) == True{} : Bool}
  {FCh.ffi(FCh.put_req(FCh.AskVerdict{c, w, e, o, m})) == FCh.put_call(Ch.verdict(c, w, e, o, m), "") : String}

# LAW: the child entry's move request answers the report phase's move
law child_entry_move:
  for +f: Maybe<&2, Ch.Fate>
  for +n: Nat
  for hn: {wire_fits(n) == True{} : Bool}
  {FCh.ffi(FCh.put_req(FCh.AskMove{f, n})) == FCh.put_move(Ch.owe.next(f, n), "") : String}

# LAW: the child entry's abort request answers the abort's phase
law child_entry_abort:
  for +p: Ch.Ph
  for +d: Bool
  for hp: {wire_ph_fits(p) == True{} : Bool}
  {FCh.ffi(FCh.put_req(FCh.AskAbort{p, d})) == FCh.put_ph(Ch.cut.ph(p, d), "") : String}

# LAW: the job entry answers the held step and the ends the event reported
law job_entry:
  for +t: Nat
  for +cap: Maybe<&2, Nat>
  for +j: Jb.J
  for +e: Jb.JEv
  for ht: {wire_fits(t) == True{} : Bool}
  for hc: {wire_mfits(cap) == True{} : Bool}
  for hj: {wire_job_fits(j) == True{} : Bool}
  for he: {wire_ev_fits(e) == True{} : Bool}
  {FJb.ffi(FJb.put_req(t, cap, j, e)) == FJb.put_reply(Jb.feed(t, cap, j, e), Jb.ends.of(j, e)) : String}

# LAW: the progress entry answers the goal's check
law goal_entry:
  for +t: Nat
  for +cap: Nat
  for +p: Maybe<&2, Pr.Prior>
  for +work: Nat
  for ht: {wire_fits(t) == True{} : Bool}
  for hc: {wire_fits(cap) == True{} : Bool}
  for hp: {wire_prior_fits(p) == True{} : Bool}
  for hw: {wire_fits(work) == True{} : Bool}
  {FPr.ffi(FPr.put_req(t, cap, p, work)) == FPr.put_goal(Pr.judge(t, cap, p, work), "") : String}

# LAW: the sandbox entry answers the plan of the path
law cow_entry:
  for +p: Maybe<&2, Nat>
  for +b: Maybe<&2, Nat>
  for +c: Maybe<&2, Nat>
  for hp: {wire_mfits(p) == True{} : Bool}
  for hb: {wire_mfits(b) == True{} : Bool}
  for hc: {wire_mfits(c) == True{} : Bool}
  {FSb.ffi(FSb.put_req(p, b, c)) == FSb.put_plan(Sb.plan(p, b, c), "") : String}
