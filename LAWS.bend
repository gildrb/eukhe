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
import ./bend/ffi_director.bend as FDr
import ./bend/ffi_child_env.bend as FEnv
import ./bend/ffi_cvar.bend as FCv
import ./bend/ffi_retry.bend as Fr
import ./bend/ffi_effort.bend as FEf
import ./bend/ffi_infer.bend as FIn
import ./bend/ffi_facts.bend as FFx
import ./bend/ffi_run.bend as FRn
import ./bend/ffi_tree.bend as Ft
import ./bend/ffi_orphan.bend as FO
import ./bend/ffi_supervise.bend as FS
import ./bend/ffi_screen.bend as FSc
import ./bend/ffi_replace.bend as FRp

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

# The compiled core: the Rust tree runs the stepper of bend/tree.bend
# (`Tr.core.step`, its state a key map and the journal) through the entry
# bend/ffi_tree.bend (laws tree_ffi_*, after section wire). Every journal
# is free: any records, valid or not; the halves hs that place the map's
# splits are free too (the Rust tree opens with 2^46, ..., 2, 1).

# the keys of the nodes of a that b does not hold, in key order
def tree.lost.at(held: Bool, k: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match held:
    case True{}:
      rest
    case False{}:
      k <> rest

def tree.lost(a: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>) -> List<&2, Nat>:
  match a:
    case Nil{}:
      Nil{}
    case +e <> rest:
      tree.lost.at(Tr.has(b, Tr.Ent.k(e)), Tr.Ent.k(e), tree.lost(rest, b))

def tree.took(good: Bool) -> Tr.Ans:
  match good:
    case True{}:
      Tr.Took{}
    case False{}:
      Tr.Kept{}

# the model's answer to record r on tree t: a put or a rewind is taken
# when the tree accepts it, else kept; a delete of the root is kept; a
# delete of any other key cuts the keys of the nodes it removes
def tree.answer(+t: List<&2, Tr.Ent>, r: Tr.Rec) -> Tr.Ans:
  match r:
    case Tr.Do{o}:
      match o:
        case Tr.Put{+k, +p, v}:
          tree.took(Tr.ok(t, k, p))
        case Tr.Del{x}:
          match x:
            case 0n:
              Tr.Kept{}
            case 1n++y:
              Tr.Cut{tree.lost(t, Tr.prune(t, 1n+y))}
    case Tr.Rewind{ops}:
      tree.took(Tr.sound(Tr.patch(ops, t)))

def tree.effect(held: Bool, k: Nat) -> Tr.Eff:
  match held:
    case True{}:
      Tr.Restore{k}
    case False{}:
      Tr.Start{k}

# what the ops of a rewind of t do to the work of each node: a Del stops
# it; a Put restores a node t has and starts one t does not have
def tree.effects(ops: List<&2, Tr.Op>, +t: List<&2, Tr.Ent>) -> List<&2, Tr.Eff>:
  match ops:
    case Nil{}:
      Nil{}
    case o <> rest:
      match o:
        case Tr.Del{k}:
          Tr.Stop{k} <> tree.effects(rest, t)
        case Tr.Put{+k, p, v}:
          tree.effect(Tr.has(t, k), k) <> tree.effects(rest, t)

# LAW: the core's tree after any journal is the tree the journal makes
law tree_core_tree:
  for +hs: List<&2, Nat>
  for +rs: List<&2, Tr.Rec>
  {Tr.KMap.read(Tr.St.m(Tr.core.feed(hs, rs))) == Tr.replay(rs) : List<&2, Tr.Ent>}

# LAW: after any journal, the core answers a record as the model decides
# it: taken or kept, and a delete cuts exactly the nodes it removes
law tree_core_answer:
  for +hs: List<&2, Nat>
  for +rs: List<&2, Tr.Rec>
  for +r: Tr.Rec
  {Pair.snd(Tr.St, Tr.Ans, Tr.core.step(Tr.core.feed(hs, rs), Tr.Note{r})) == tree.answer(Tr.replay(rs), r) : Tr.Ans}

# LAW: a record steps the core to the core of the journal with the record
# at its end, so the laws on core.feed hold for the live core
law tree_core_note:
  for +hs: List<&2, Nat>
  for +rs: List<&2, Tr.Rec>
  for +r: Tr.Rec
  {Pair.fst(Tr.St, Tr.Ans, Tr.core.step(Tr.core.feed(hs, rs), Tr.Note{r})) == Tr.core.feed(hs, List.append(&2, Tr.Rec, rs, [r])) : Tr.St}

# LAW: the core's rewind plan to the tree after the first n records is
# what diff(live tree, that tree) does to the work of each node
law tree_core_plan:
  for +hs: List<&2, Nat>
  for +rs: List<&2, Tr.Rec>
  for +n: Nat
  {Pair.snd(Tr.St, Tr.Ans, Tr.core.step(Tr.core.feed(hs, rs), Tr.Plan{n})) == Tr.Effects{tree.effects(Tr.diff(Tr.replay(rs), Tr.replay(List.take(&2, Tr.Rec, rs, n))), Tr.replay(rs))} : Tr.Ans}

# LAW: the core's snapshot after the first n records is their replay
law tree_core_snap:
  for +hs: List<&2, Nat>
  for +rs: List<&2, Tr.Rec>
  for +n: Nat
  {Pair.snd(Tr.St, Tr.Ans, Tr.core.step(Tr.core.feed(hs, rs), Tr.Snap{n})) == Tr.Nodes{Tr.replay(List.take(&2, Tr.Rec, rs, n))} : Tr.Ans}

# LAW: a rewind plan leaves the core as it was
law tree_core_plan_keeps:
  for +hs: List<&2, Nat>
  for +rs: List<&2, Tr.Rec>
  for +n: Nat
  {Pair.fst(Tr.St, Tr.Ans, Tr.core.step(Tr.core.feed(hs, rs), Tr.Plan{n})) == Tr.core.feed(hs, rs) : Tr.St}

# LAW: a snapshot leaves the core as it was
law tree_core_snap_keeps:
  for +hs: List<&2, Nat>
  for +rs: List<&2, Tr.Rec>
  for +n: Nat
  {Pair.fst(Tr.St, Tr.Ans, Tr.core.step(Tr.core.feed(hs, rs), Tr.Snap{n})) == Tr.core.feed(hs, rs) : Tr.St}

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
# the deciding one too) holds fewer than cap layers. A cap the Rust code
# saturates (at the wire's largest Nat) leaves room for every stack.
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

# LAW: the guarded share is the plain formula, for every minimum, lag and
# backlog: a frame reveals min(b, max(min, b / (1 + k)))
# EXCLUDES: a guard (no 1 + k formed when k >= b) that changes the
# reveal for some lag
law pace_reveal_formula:
  for +min: Nat
  for +k: Nat
  for +b: Nat
  {Sc.reveal(min, k, b) == Nat.min(b, Nat.max(min, Nat.div(b, 1n+k))) : Nat}

# LAW: a lag at least the backlog reveals the minimum (the whole backlog
# when it is smaller). Rust saturates the lag at the cap of the compiled
# core's numbers (2^48 - 1), which is at least every backlog it holds: a
# lag at the cap reveals the minimum
# EXCLUDES: a capped lag that reveals more than the minimum, or nothing
law pace_lag_at_cap:
  for +min: Nat
  for +k: Nat
  for +b: Nat
  for capped: {Nat.is_le(b, k) == True{} : Bool}
  {Sc.reveal(min, k, b) == Nat.min(b, min) : Nat}

# every block of bs is committed
def all_comm(bs: List<&2, Sc.Blk>) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case b <> rest:
      match b:
        case Sc.Blk{i, s, l}:
          match s:
            case Sc.Comm{}:
              all_comm(rest)
            case Sc.Final{}:
              False{}
            case Sc.Active{}:
              False{}

# the transcript t with the blocks cs before its blocks
def under(cs: List<&2, Sc.Blk>, t: Sc.Tx) -> Sc.Tx:
  match t:
    case Sc.Tx{bs, n, w}:
      Sc.Tx{List.append(&2, Sc.Blk, cs, bs), n, w}

# LAW: committed blocks are inert. Any events on a transcript whose
# blocks start with committed blocks cs give the transcript the same
# events give without cs, with cs in front. So the core runs on the blocks
# after the committed prefix alone (Rust sends only those)
# EXCLUDES: an event that changes, drops or moves a committed block, and
# a result that depends on the committed blocks
law tx_committed_inert:
  for es: List<&2, Sc.Ev>
  for +cs: List<&2, Sc.Blk>
  for +bs: List<&2, Sc.Blk>
  for +n: Nat
  for +w: Nat
  for comm: {all_comm(cs) == True{} : Bool}
  {Sc.run(es, Sc.Tx{List.append(&2, Sc.Blk, cs, bs), n, w}) == under(cs, Sc.run(es, Sc.Tx{bs, n, w})) : Sc.Tx}

# LAW: the premise of tx_committed_inert holds for a real prefix
# EXCLUDES: an all_comm that is never True (a vacuous inert law)
law all_comm_example:
  {all_comm([Sc.Blk{0n, Sc.Comm{}, 3n}, Sc.Blk{1n, Sc.Comm{}, 0n}]) == True{} : Bool}

# LAW: a prefix with a final or an active block is not committed
# EXCLUDES: an all_comm that is always True
law all_comm_rejects:
  {Bool.or(all_comm([Sc.Blk{0n, Sc.Final{}, 0n}]), all_comm([Sc.Blk{0n, Sc.Comm{}, 0n}, Sc.Blk{1n, Sc.Active{}, 0n}])) == False{} : Bool}

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

# (H4.9) The decisions Rust calls are the model's
# -----------------------------------------------
# docs/harness.md H4, the decisions of bend/run.bend that
# crates/eukhe-durable/src/harness/generation/decide.rs and deferred.rs
# call through the compiled core (decide.reply, decide.prepare,
# decide.compact, decide.round, decide.poll; decide.recover in section
# recover). Rust keeps its counters as they grow (Counts, Rounds); each
# decision makes the counts left of the model from them, takes the
# model's step and reads its answer back. The helpers rust.* are the
# rules as decide.rs and deferred.rs wrote them before the core took
# them over, over the counts that grow. The laws prove every decision
# equal to its rule for every input (the projection is exact), the
# counts left lose nothing of the counts Rust keeps, they count down
# exactly as Rust's counts grow, a failed poll and a deferred reply do
# what the deferred job of bend/retry.bend section 4 does, and the cap
# Rust saturates its 64-bit counts at (the wire's largest Nat, below the
# core's Nat range) changes no decision.

# the step after a deferred reply, as `after_reply` took it: poll the
# same job while the request waited less than the job may run
def rust.wait(waits: Bool) -> Rn.Then:
  match waits:
    case True{}:
      Rn.DoPoll{}
    case False{}:
      Rn.DoLate{}

# a noted reply retries with a note while notes are left
def rust.noted(left: Bool) -> Rn.Then:
  match left:
    case True{}:
      Rn.DoNote{}
    case False{}:
      Rn.DoFail{}

# an error that is not noted retries while it is retryable and retries
# are left
def rust.retry(left: Bool) -> Rn.Then:
  match left:
    case True{}:
      Rn.DoRetry{}
    case False{}:
      Rn.DoFail{}

# an overflow compacts when a cut exists and the generation has not
# compacted
def rust.over(compacts: Bool) -> Rn.Then:
  match compacts:
    case True{}:
      Rn.DoCompact{}
    case False{}:
      Rn.DoFail{}

# `after_reply`: the retries spent are the attempts after the first that
# were not noted, (attempt - 1) - notes
def rust.after_reply(l: Rn.Lim, t: Rn.At, reply: Rn.Reply) -> Rn.Then:
  match l:
    case Rn.Lim{rounds, wait, retries, most}:
      match t:
        case Rn.At{attempt, +notes, waited, compacted}:
          match reply:
            case Rn.Plain{}:
              Rn.DoAnswer{}
            case Rn.Calls{}:
              Rn.DoTools{}
            case Rn.Deferred{}:
              rust.wait(Nat.is_lt(waited, wait))
            case Rn.Error{retryable, noted}:
              match noted:
                case True{}:
                  rust.noted(Nat.is_lt(notes, most))
                case False{}:
                  rust.retry(Bool.and(retryable, Nat.is_lt(Nat.sub(Nat.sub(attempt, 1n), notes), retries)))
            case Rn.Overflow{cut}:
              rust.over(Bool.and(cut, Bool.not(compacted)))

# LAW: the step after any reply, from any counts and limits, is the one
# `after_reply` took: the counts left that the model reads (At.a, At.n,
# At.p, At.c) are exact
law run_reply_is_the_rust_rule:
  for +l: Rn.Lim
  for +t: Rn.At
  for +reply: Rn.Reply
  {Rn.decide.reply(l, t, reply) == rust.after_reply(l, t, reply) : Rn.Then}

# `before_request`: a generation that compacted sends its request with no
# compaction; else a context over the blocking threshold (with a cut)
# waits for a compaction, and one over the background threshold sends
# with a background compaction beside it
def rust.before_request(compacted: Bool, th: Rn.Th) -> Rn.Prepared:
  match compacted:
    case True{}:
      Rn.Sends{False{}}
    case False{}:
      match th:
        case Rn.Under{}:
          Rn.Sends{False{}}
        case Rn.Background{}:
          Rn.Sends{True{}}
        case Rn.Blocking{}:
          Rn.Waits{}

# LAW: what preparation does, for every generation and every threshold,
# is what `before_request` did
law run_prepare_is_the_rust_rule:
  for +compacted: Bool
  for +th: Rn.Th
  {Rn.decide.prepare(compacted, th) == rust.before_request(compacted, th) : Rn.Prepared}

# LAW: a generation that compacted reads no threshold: whatever its
# context is over, it prepares as if under every threshold. So Rust need
# not measure the context (a provider's count is a request) after the
# generation compacted
law run_prepare_compacted_reads_no_threshold:
  for +th: Rn.Th
  {Rn.decide.prepare(True{}, th) == Rn.decide.prepare(True{}, Rn.Under{}) : Rn.Prepared}

# `after_compaction`: an entry goes on; a threshold compaction that
# found nothing goes on; an overflow's that found nothing, or any that
# failed, fails the run
def rust.after_compaction(over: Bool, got: Rn.Got) -> Bool:
  match over got:
    case over Rn.Built{}:
      True{}
    case True{} Rn.Kept{}:
      False{}
    case False{} Rn.Kept{}:
      True{}
    case over Rn.Broke{}:
      False{}

# LAW: whether preparation goes on after any compaction is what
# `after_compaction` decided
law run_compact_is_the_rust_rule:
  for +over: Bool
  for +got: Rn.Got
  {Rn.decide.compact(over, got) == rust.after_compaction(over, got) : Bool}

# a round that the cap lets go on hands the run on with one more round,
# unless a queued reset ends it
def rust.next(goes: Bool, reset: Bool, count: Nat) -> Rn.End:
  match goes:
    case True{}:
      match reset:
        case True{}:
          Rn.EndReset{}
        case False{}:
          Rn.EndNext{1n+count}
    case False{}:
      Rn.EndCapped{}

# `Rounds::finish` then `RoundEnd::reset`: a control stops the run; else
# the round after count rounds is capped at maxToolRounds
def rust.round_end(l: Rn.Lim, +count: Nat, stops: Bool, reset: Bool) -> Rn.End:
  match l:
    case Rn.Lim{rounds, wait, retries, most}:
      match stops:
        case True{}:
          Rn.EndStop{}
        case False{}:
          rust.next(Nat.is_lt(1n+count, rounds), reset, count)

# LAW: how any round ends, after any rounds, under any cap, is what
# `Rounds::finish` and `RoundEnd::reset` decided
law run_round_is_the_rust_rule:
  for +l: Rn.Lim
  for +count: Nat
  for +stops: Bool
  for +reset: Bool
  {Rn.decide.round(l, count, stops, reset) == rust.round_end(l, count, stops, reset) : Rn.End}

# LAW: a round that no control stops leaves the rounds left of the run of
# count + 1 rounds: the model counts down as Rust counts up
law run_round_counts_down:
  for +l: Rn.Lim
  for +count: Nat
  for +reset: Bool
  for +c: Nat
  for +a: Nat
  for +n: Nat
  for +p: Nat
  {Rn.St.r(Rn.tools(Rn.Lim.cfg(l), Rn.fin.of(False{}, reset), Rn.Lim.r(l, count), c, a, n, p)) == Rn.Lim.r(l, 1n+count) : Nat}

# the counts of the request a noted retry sends: one more attempt and
# one more note (`retry_note`, then the retry phase)
def rust.noted_next(t: Rn.At) -> Rn.At:
  match t:
    case Rn.At{attempt, notes, waited, compacted}:
      Rn.At{1n+attempt, 1n+notes, 0n, compacted}

# the counts of the request a transient retry sends: one more attempt
def rust.retried_next(t: Rn.At) -> Rn.At:
  match t:
    case Rn.At{attempt, notes, waited, compacted}:
      Rn.At{1n+attempt, notes, 0n, compacted}

# LAW: a noted reply leaves the notes left of the request its retry
# sends
law run_note_counts_down:
  for +l: Rn.Lim
  for +t: Rn.At
  for +r: Nat
  for +c: Nat
  for +p: Nat
  {Rn.St.n(Rn.note(Rn.Lim.cfg(l), r, c, Rn.At.a(l, t), Rn.At.n(l, t), p)) == Rn.At.n(l, rust.noted_next(t)) : Nat}

# LAW: a noted reply leaves the retries left of the request its retry
# sends: a note spends no retry
law run_note_keeps_the_retries:
  for +l: Rn.Lim
  for +t: Rn.At
  for +r: Nat
  for +c: Nat
  for +p: Nat
  {Rn.St.a(Rn.note(Rn.Lim.cfg(l), r, c, Rn.At.a(l, t), Rn.At.n(l, t), p)) == Rn.At.a(l, rust.noted_next(t)) : Nat}

# LAW: a retryable error leaves the retries left of the request its retry
# sends, for every request whose attempts count its notes (attempt >=
# 1 + notes, as every request of a generation has)
law run_retry_counts_down:
  for +l: Rn.Lim
  for +t: Rn.At
  for +e: {Nat.is_le(1n+Rn.At.notes(t), Rn.At.attempt(t)) == True{} : Bool}
  for +r: Nat
  for +c: Nat
  for +p: Nat
  {Rn.St.a(Rn.retry(Rn.Lim.cfg(l), True{}, r, c, Rn.At.a(l, t), Rn.At.n(l, t), p)) == Rn.At.a(l, rust.retried_next(t)) : Nat}

# LAW: witness: a request whose attempts count its notes exists
law run_retry_premise_witness:
  exs t: Rn.At
  {Nat.is_le(1n+Rn.At.notes(t), Rn.At.attempt(t)) == True{} : Bool}

# LAW: a retryable error leaves the notes left of the request its retry
# sends: a retry spends no note
law run_retry_keeps_the_notes:
  for +l: Rn.Lim
  for +t: Rn.At
  for +r: Nat
  for +c: Nat
  for +p: Nat
  {Rn.St.n(Rn.retry(Rn.Lim.cfg(l), True{}, r, c, Rn.At.a(l, t), Rn.At.n(l, t), p)) == Rn.At.n(l, rust.retried_next(t)) : Nat}

# the counts of a request within its limits: notes at most MAX_NOTES,
# an attempt per note and one more, retries spent at most
# retry.maxRetries, the ms waited at most the job's
def rust.within(l: Rn.Lim, t: Rn.At) -> Bool:
  match l:
    case Rn.Lim{rounds, wait, retries, most}:
      match t:
        case Rn.At{+attempt, +notes, waited, compacted}:
          Bool.and(Nat.is_le(notes, most), Bool.and(Nat.is_le(1n+notes, attempt), Bool.and(Nat.is_le(Nat.sub(Nat.sub(attempt, 1n), notes), retries), Nat.is_le(waited, wait))))

# the counts Rust keeps, read back from the counts left
def rust.back(l: Rn.Lim, a: Nat, +n: Nat, p: Nat, c: Nat) -> Rn.At:
  match l:
    case Rn.Lim{rounds, wait, retries, +most}:
      Rn.At{1n+Nat.add(Nat.sub(retries, a), Nat.sub(most, n)), Nat.sub(most, n), Nat.sub(wait, p), Nat.is_eq(c, 0n)}

# LAW: the counts left lose nothing: within its limits, a request's
# counts come back from the counts left the model reads
law run_counts_lossless:
  for +l: Rn.Lim
  for +t: Rn.At
  for +w: {rust.within(l, t) == True{} : Bool}
  {rust.back(l, Rn.At.a(l, t), Rn.At.n(l, t), Rn.At.p(l, t), Rn.At.c(t)) == t : Rn.At}

# LAW: witness: counts within their limits exist
law run_counts_within_witness:
  exs l: Rn.Lim
  exs t: Rn.At
  {rust.within(l, t) == True{} : Bool}

# LAW: the rounds left lose nothing: below the cap, the rounds made come
# back from the rounds left
law run_rounds_lossless:
  for +l: Rn.Lim
  for +count: Nat
  for +w: {Nat.is_lt(count, Rn.Lim.rounds(l)) == True{} : Bool}
  {Nat.sub(Nat.sub(Rn.Lim.rounds(l), 1n), Rn.Lim.r(l, count)) == count : Nat}

# LAW: witness: a run below its round cap exists
law run_rounds_within_witness:
  exs l: Rn.Lim
  exs count: Nat
  {Nat.is_lt(count, Rn.Lim.rounds(l)) == True{} : Bool}

# what a failed poll of a live job does in Rust: poll again when
# `PollFailure::next` repolls and the poll's time check (a deferred reply)
# polls; else cancel the job
def rust.job(repoll: Bool, t: Rn.Then) -> R.Act:
  match repoll:
    case True{}:
      match t:
        case Rn.DoPoll{}:
          R.Poll{}
        case Rn.DoAnswer{}:
          R.Cancel{}
        case Rn.DoTools{}:
          R.Cancel{}
        case Rn.DoRetry{}:
          R.Cancel{}
        case Rn.DoNote{}:
          R.Cancel{}
        case Rn.DoCompact{}:
          R.Cancel{}
        case Rn.DoFail{}:
          R.Cancel{}
        case Rn.DoLate{}:
          R.Cancel{}
    case False{}:
      R.Cancel{}

# what a deferred reply does to the job in Rust: poll again, or cancel it
# at its deadline
def rust.later(t: Rn.Then) -> R.Act:
  match t:
    case Rn.DoPoll{}:
      R.Poll{}
    case Rn.DoAnswer{}:
      R.Cancel{}
    case Rn.DoTools{}:
      R.Cancel{}
    case Rn.DoRetry{}:
      R.Cancel{}
    case Rn.DoNote{}:
      R.Cancel{}
    case Rn.DoCompact{}:
      R.Cancel{}
    case Rn.DoFail{}:
      R.Cancel{}
    case Rn.DoLate{}:
      R.Cancel{}

# LAW: a failed poll of a live job, from any counts, does what the job of
# bend/retry.bend section 4 does with the ms left (wait - waited): it
# polls the same job again exactly when that job does
law run_failed_poll_is_the_job_model:
  for +l: Rn.Lim
  for +t: Rn.At
  for +retryable: Bool
  for +failed: Nat
  for +budget: Nat
  for +gap: Nat
  {rust.job(Rn.decide.poll(retryable, failed, Rn.Lim.retries(l)), Rn.decide.reply(l, t, Rn.Deferred{})) == R.Step.act(R.step(Rn.Lim.retries(l), budget, R.Live{failed, Rn.At.p(l, t)}, R.Broke{retryable, gap})) : R.Act}

# LAW: a deferred reply to a poll of a live job, from any counts, does
# what the job of bend/retry.bend section 4 does with the ms left: it
# polls again exactly when that job does, else the job is cancelled at
# its deadline
law run_deferred_reply_is_the_job_model:
  for +l: Rn.Lim
  for +t: Rn.At
  for +fails: Nat
  for +budget: Nat
  for +failed: Nat
  for +gap: Nat
  {rust.later(Rn.decide.reply(l, t, Rn.Deferred{})) == R.Step.act(R.step(fails, budget, R.Live{failed, Rn.At.p(l, t)}, R.Later{gap})) : R.Act}

# LAW: the first deferred reply of a request does what the job of
# bend/retry.bend section 4 does with a new job of the ms left
law run_first_deferred_reply_is_the_job_model:
  for +l: Rn.Lim
  for +t: Rn.At
  for +fails: Nat
  for +gap: Nat
  {rust.later(Rn.decide.reply(l, t, Rn.Deferred{})) == R.Step.act(R.step(fails, Rn.At.p(l, t), R.NoJob{}, R.Later{gap})) : R.Act}

# the limits with the job's ms saturated at cap
def rust.sat_wait(l: Rn.Lim, +cap: Nat) -> Rn.Lim:
  match l:
    case Rn.Lim{rounds, wait, retries, most}:
      Rn.Lim{rounds, Nat.min(wait, cap), retries, most}

# the counts with the attempt saturated at cap
def rust.sat_attempt(t: Rn.At, +cap: Nat) -> Rn.At:
  match t:
    case Rn.At{attempt, notes, waited, compacted}:
      Rn.At{Nat.min(attempt, cap), notes, waited, compacted}

# LAW: Rust saturates the job's ms and the ms waited (u64s) at the wire's
# largest Nat (10^14 - 1) before it encodes them: for a request that
# waited less than any cap (10^14 ms is 3000 years), the step after any
# reply is the same. A wait at the cap never ends a job that waited less
law run_reply_saturates_the_wait:
  for +l: Rn.Lim
  for +t: Rn.At
  for +reply: Rn.Reply
  for +cap: Nat
  for +e: {Nat.is_lt(Rn.At.waited(t), cap) == True{} : Bool}
  {Rn.decide.reply(rust.sat_wait(l, cap), t, reply) == Rn.decide.reply(l, t, reply) : Rn.Then}

# LAW: Rust saturates the attempt (a u64) at the wire's largest Nat: any
# cap above notes + retry.maxRetries (two u32s) leaves the step after any
# reply the same (an attempt at the cap has spent every retry, as a
# larger one)
law run_reply_saturates_the_attempt:
  for +l: Rn.Lim
  for +t: Rn.At
  for +reply: Rn.Reply
  for +cap: Nat
  for +e: {Nat.is_lt(Nat.add(Rn.At.notes(t), Rn.Lim.retries(l)), cap) == True{} : Bool}
  {Rn.decide.reply(l, rust.sat_attempt(t, cap), reply) == Rn.decide.reply(l, t, reply) : Rn.Then}

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

# (T1) Color text, value resolution, file reading, completion, picking
# ---------------------------------------------------------------------
# The rules of crates/eukhe-theme that the user sees: which text is a
# color, how a value follows the variables, the error a broken file
# reports (one per kind, never a default), the palette a file completes
# to, and the theme a name picks with its warnings. Requirements:
# R1 a color is "" (the terminal default), an integer 0-255 (an xterm-256
#    index) or #rrggbb (either case); every other value is an error that
#    names it: "Invalid hex color" for a #-string, "Invalid color value"
#    for the rest.
# R2 any other string names a variable; a missing one is "Variable
#    reference not found: <name>", the first one met twice on the chain is
#    "Circular variable reference detected: <name>".
# R3 a file reports the first error of its colors in key order (a key
#    that names no token: "unknown color token"), then the required tokens
#    it does not write, in token order, then the errors of its export
#    page, card and info backgrounds, in that order.
# R4 a file that reads completes: written tokens keep their value, mdBody
#    falls back to text, the refinement pair and foreground to the
#    builtin of the file's mode, the background to the file's background,
#    export page, user-message surface, default theme's background.
# R5 a name picks as the laws above say; a name that picks no theme
#    warns with the first file that did not load and advertises it (or,
#    no theme object, is named after it); every other file that did not
#    load warns once; a valid file whose name an earlier valid file has
#    clashes with the first of them.
# A1 Rust decodes the JSON (serde) and projects it losslessly: keys in
#    order, each string with the index of the variable it names, numbers
#    and other values as JSON writes them (the projection is glue the
#    Rust tests check, the laws cannot see it).

# x is in xs
def th.mem(xs: List<&2, Nat>, +x: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{y, rest}:
      Bool.or(Nat.is_eq(y, x), th.mem(rest, x))

def th.val(m: Maybe<&2, T.Var>) -> Maybe<&2, T.Json>:
  match m:
    case None{}:
      None{}
    case Some{v}:
      match v:
        case T.Var{nm, j}:
          Some{j}

# the value of variable i
def th.var(+xs: List<&2, T.Var>, i: Nat) -> Maybe<&2, T.Json>:
  th.val(List.get(&2, T.Var, xs, i))

def th.hex(m: Maybe<&2, Co.Rgb>, s: String) -> T.Got:
  match m:
    case None{}:
      T.Miss{T.BadHex{s}}
    case Some{c}:
      T.Hit{T.Hex{c}}

def th.num(m: Maybe<&2, U32>, s: String) -> T.Got:
  match m:
    case None{}:
      T.Miss{T.BadValue{s}}
    case Some{i}:
      T.Hit{T.Idx{i}}

# a name met before is a cycle; else a missing variable, else its value
def th.ref(looped: Bool, found: Maybe<&2, T.Json>, seen: List<&2, Nat>, s: String, i: Nat) -> T.Step:
  match looped:
    case True{}:
      T.Stop{T.Miss{T.Circular{s}}}
    case False{}:
      match found:
        case None{}:
          T.Stop{T.Miss{T.NotFound{s}}}
        case Some{j}:
          T.Go{i <> seen, j}

def th.name(+vars: List<&2, T.Var>, +seen: List<&2, Nat>, s: String, at: Maybe<&2, Nat>) -> T.Step:
  match at:
    case None{}:
      T.Stop{T.Miss{T.NotFound{s}}}
    case Some{+i}:
      th.ref(th.mem(seen, i), th.var(vars, i), seen, s, i)

def th.text.c(sharp: Bool, +vars: List<&2, T.Var>, +seen: List<&2, Nat>, +s: String, at: Maybe<&2, Nat>) -> T.Step:
  match sharp:
    case True{}:
      T.Stop{th.hex(Co.hex(s), s)}
    case False{}:
      th.name(vars, seen, s, at)

def th.text(+vars: List<&2, T.Var>, +seen: List<&2, Nat>, s: String, at: Maybe<&2, Nat>) -> T.Step:
  match s:
    case SNil{}:
      T.Stop{T.Hit{T.Dflt{}}}
    case SCon{+c, rest}:
      th.text.c(Char.is_eq(c, '#'), vars, seen, SCon{c, rest}, at)

# one step of the rule of crates/eukhe-theme (resolve_var_refs, then
# color_value): "" is the terminal default, a #-string must be #rrggbb,
# any other string names a variable (met before on the chain: a cycle;
# missing: not found); a number must be 0-255; anything else is no color
def th.next(+vars: List<&2, T.Var>, +seen: List<&2, Nat>, j: T.Json) -> T.Step:
  match j:
    case T.JStr{s, at}:
      th.text(vars, seen, s, at)
    case T.JNum{+t}:
      T.Stop{th.num(Co.num(t), t)}
    case T.JOther{t}:
      T.Stop{T.Miss{T.BadValue{t}}}

def th.follow(fuel: Nat, +vars: List<&2, T.Var>, st: T.Step) -> T.Got:
  match fuel:
    case 0n:
      match st:
        case T.Stop{g}:
          g
        case T.Go{seen, j}:
          T.Miss{T.Circular{""}}
    case 1n+f:
      match st:
        case T.Stop{g}:
          g
        case T.Go{seen, j}:
          th.follow(f, vars, th.next(vars, seen, j))

# the color a value resolves to: the rule's steps from no variable met;
# each step past the first meets a new variable, so one step more than
# there are variables reaches the end
def th.chase(+vars: List<&2, T.Var>, j: T.Json) -> T.Got:
  th.follow(1n+List.length(&2, T.Var, vars), vars, T.Go{Nil{}, j})

def th.is(m: Maybe<&2, U32>, +v: U32) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      U32.is_eq(x, v)

# every index from v on, k of them, written in decimal reads back
def th.nums(k: Nat, +v: U32) -> Bool:
  match k:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(th.is(Co.num(U32.show(v)), v), th.nums(p, (v + 1 : U32)))

# s has seven characters, the first a #
def th.sharp7(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{h, s1}:
      match s1:
        case SNil{}:
          False{}
        case SCon{a, s2}:
          match s2:
            case SNil{}:
              False{}
            case SCon{b, s3}:
              match s3:
                case SNil{}:
                  False{}
                case SCon{c, s4}:
                  match s4:
                    case SNil{}:
                      False{}
                    case SCon{d, s5}:
                      match s5:
                        case SNil{}:
                          False{}
                        case SCon{e, s6}:
                          match s6:
                            case SNil{}:
                              False{}
                            case SCon{f, s7}:
                              match s7:
                                case SNil{}:
                                  Char.is_eq(h, '#')
                                case SCon{g, s8}:
                                  False{}

# every xterm-256 color from index i on, k of them, quantizes to its own
# index
def th.fixed(k: Nat, +i: U32) -> Bool:
  match k:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(U32.is_eq(Co.to256(Co.ansi256(i)), i), th.fixed(p, (i + 1 : U32)))

def th.good(r: T.EntR) -> Bool:
  match r:
    case T.Good{e}:
      True{}
    case T.Bad{f}:
      False{}

# every entry of es reads
def th.clean(+vars: List<&2, T.Var>, es: List<&2, T.REnt>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case Con{e, rest}:
      Bool.and(th.good(T.entry(vars, e)), th.clean(vars, rest))

def th.ent(r: T.EntR) -> T.Ent:
  match r:
    case T.Good{e}:
      e
    case T.Bad{f}:
      T.Ent{0, T.Dflt{}}

# the entries es read (when every one reads)
def th.goods(+vars: List<&2, T.Var>, es: List<&2, T.REnt>) -> List<&2, T.Ent>:
  match es:
    case Nil{}:
      Nil{}
    case Con{e, rest}:
      th.ent(T.entry(vars, e)) <> th.goods(vars, rest)

# the tokens every file must write: all but refinementHeader (14),
# refinementSummary (15), mdBody (18), background (57), foreground (58)
def th.required() -> List<&2, U32>:
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 16, 17, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56]

def th.keep(keep: Bool, t: U32, rest: List<&2, U32>) -> List<&2, U32>:
  match keep:
    case True{}:
      t <> rest
    case False{}:
      rest

def th.absent.go(+es: List<&2, T.Ent>, ts: List<&2, U32>) -> List<&2, U32>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{+t, rest}:
      th.keep(Bool.not(Maybe.is_some(&2, T.Val, T.get(es, t))), t, th.absent.go(es, rest))

# the required tokens es does not write, in token order
def th.absent(+es: List<&2, T.Ent>) -> List<&2, U32>:
  th.absent.go(es, th.required())

def th.reqs(ts: List<&2, U32>) -> List<&2, U32>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{+t, rest}:
      th.keep(T.required(t), t, th.reqs(rest))

def th.hit(g: T.Got) -> Bool:
  match g:
    case T.Hit{v}:
      True{}
    case T.Miss{why}:
      False{}

# an export background that reads: unset, or a color
def th.fine(+vars: List<&2, T.Var>, m: Maybe<&2, T.Json>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{j}:
      th.hit(T.chase(vars, j))

def th.hitc(g: T.Got) -> Maybe<&2, Co.Rgb>:
  match g:
    case T.Hit{v}:
      T.concrete(v)
    case T.Miss{why}:
      None{}

# the color an export background sets: none when unset or ""
def th.bgv(+vars: List<&2, T.Var>, m: Maybe<&2, T.Json>) -> Maybe<&2, Co.Rgb>:
  match m:
    case None{}:
      None{}
    case Some{j}:
      th.hitc(T.chase(vars, j))

# the file's own background as #rrggbb: an index or "" is none
def th.own(m: Maybe<&2, T.Val>) -> Maybe<&2, Co.Rgb>:
  match m:
    case None{}:
      None{}
    case Some{v}:
      match v:
        case T.Dflt{}:
          None{}
        case T.Idx{i}:
          None{}
        case T.Hex{c}:
          Some{c}

# the files of one source (custom or registered) that load, in order, as
# candidates after the builtins (ids 0..2): the file at index i is 3 + i
def th.cand(l: T.Ld, +custom: Bool, at: Nat) -> List<&2, T.Cand>:
  match l:
    case T.Fine{nm, c}:
      match c:
        case True{}:
          match custom:
            case True{}:
              [T.Cand{nm, True{}, U32.from_nat(Nat.add(3n, at))}]
            case False{}:
              []
        case False{}:
          match custom:
            case True{}:
              []
            case False{}:
              [T.Cand{nm, True{}, U32.from_nat(Nat.add(3n, at))}]
    case T.Broke{nm, st}:
      []

def th.cands(ls: List<&2, T.Ld>, +custom: Bool, +at: Nat) -> List<&2, T.Cand>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{l, rest}:
      List.append(&2, T.Cand, th.cand(l, custom, at), th.cands(rest, custom, 1n+at))

# the theme a name picks over the files
def th.pick(+ls: List<&2, T.Ld>, +n: String) -> T.Res:
  T.resolve.name(T.sources(th.cands(ls, False{}, 0n), th.cands(ls, True{}, 0n)), n)

def th.same(m: Maybe<&2, String>, +n: String) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      String.eq(x, n)

# a file that did not load blames name n: it advertises n, or it is no
# theme object and its stem is n
def th.blames(l: T.Ld, +n: String) -> Bool:
  match l:
    case T.Fine{nm, c}:
      False{}
    case T.Broke{nm, st}:
      match nm:
        case Some{x}:
          String.eq(x, n)
        case None{}:
          th.same(st, n)

def th.at.if(hit: Bool, at: Nat, other: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match hit:
    case True{}:
      Some{at}
    case False{}:
      other

# the index of the first file that blames n (the first is at index at)
def th.blame(ls: List<&2, T.Ld>, +n: String, +at: Nat) -> Maybe<&2, Nat>:
  match ls:
    case Nil{}:
      None{}
    case Con{l, rest}:
      th.at.if(th.blames(l, n), at, th.blame(rest, n, 1n+at))

# the skipped failure: the cause of a warning, none without one
def th.skip(w: Bool, m: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match w:
    case True{}:
      m
    case False{}:
      None{}

def th.cause.of(m: Maybe<&2, Nat>) -> T.Cause:
  match m:
    case None{}:
      T.NoTheme{}
    case Some{at}:
      T.FailedAt{at}

def th.is.at(m: Maybe<&2, Nat>, +at: Nat) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      Nat.is_eq(x, at)

def th.broke(l: T.Ld) -> Bool:
  match l:
    case T.Fine{nm, c}:
      False{}
    case T.Broke{nm, st}:
      True{}

def th.keepn(keep: Bool, at: Nat) -> List<&2, Nat>:
  match keep:
    case True{}:
      [at]
    case False{}:
      []

# the indices of the files that did not load, but skip
def th.broken(ls: List<&2, T.Ld>, +skip: Maybe<&2, Nat>, +at: Nat) -> List<&2, Nat>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{l, rest}:
      List.append(&2, Nat, th.keepn(Bool.and(th.broke(l), Bool.not(th.is.at(skip, at))), at), th.broken(rest, skip, 1n+at))

def th.named(l: T.Ld, +n: String) -> Bool:
  match l:
    case T.Fine{nm, c}:
      String.eq(nm, n)
    case T.Broke{nm, st}:
      False{}

# the index of the first loaded file named n (the first is at index at)
def th.first(ls: List<&2, T.Ld>, +n: String, +at: Nat) -> Maybe<&2, Nat>:
  match ls:
    case Nil{}:
      None{}
    case Con{l, rest}:
      th.at.if(th.named(l, n), at, th.first(rest, n, 1n+at))

def th.clash.if(same: Bool, w: Nat, at: Nat) -> List<&2, T.Clash>:
  match same:
    case True{}:
      []
    case False{}:
      [T.Clash{at, w}]

def th.clash(m: Maybe<&2, Nat>, +at: Nat) -> List<&2, T.Clash>:
  match m:
    case None{}:
      []
    case Some{+w}:
      th.clash.if(Nat.is_eq(w, at), w, at)

# every loaded file at index i whose name the loaded file at an earlier
# index j has first: Clash{i, j}, in file order
def th.clashes.go(+all: List<&2, T.Ld>, ls: List<&2, T.Ld>, +at: Nat) -> List<&2, T.Clash>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{l, rest}:
      match l:
        case T.Fine{+nm, c}:
          List.append(&2, T.Clash, th.clash(th.first(all, nm, 0n), at), th.clashes.go(all, rest, 1n+at))
        case T.Broke{nm, st}:
          th.clashes.go(all, rest, 1n+at)

def th.clashes(+ls: List<&2, T.Ld>) -> List<&2, T.Clash>:
  th.clashes.go(ls, ls, 0n)

def th.res(p: T.Pick) -> T.Res:
  match p:
    case T.Pick{r, c, k, b}:
      r

def th.cause(p: T.Pick) -> Maybe<&2, T.Cause>:
  match p:
    case T.Pick{r, c, k, b}:
      c

def th.clashes.of(p: T.Pick) -> List<&2, T.Clash>:
  match p:
    case T.Pick{r, c, k, b}:
      k

def th.broken.of(p: T.Pick) -> List<&2, Nat>:
  match p:
    case T.Pick{r, c, k, b}:
      b

# Color text

# LAW R1 the strict #rrggbb form: a # and six hex digits, either case
# EXCLUDES: a parser that accepts #rgb, a missing #, a non-hex digit, a
#   seventh digit, or reads digits in the wrong order or channel
law theme_hex_example:
  {[Co.hex("#0A0b0c"), Co.hex("#abc"), Co.hex("0a0b0c"), Co.hex("#0a0b0g"), Co.hex("#0a0b0c0"), Co.hex("#ffFF00")] == [Some{Co.Rgb{10, 11, 12}}, None{}, None{}, None{}, None{}, Some{Co.Rgb{255, 255, 0}}] : List<&2, Maybe<&2, Co.Rgb>>}

# LAW R1 the hex digits: 0-9, a-f and A-F, and nothing next to them
# EXCLUDES: a digit table with a wrong or missing digit, a case that does
#   not read, a neighbor of a digit range read as a digit
law theme_hex_digits:
  {[Co.hexd('0'), Co.hexd('1'), Co.hexd('2'), Co.hexd('3'), Co.hexd('4'), Co.hexd('5'), Co.hexd('6'), Co.hexd('7'), Co.hexd('8'), Co.hexd('9'), Co.hexd('a'), Co.hexd('b'), Co.hexd('c'), Co.hexd('d'), Co.hexd('e'), Co.hexd('f'), Co.hexd('A'), Co.hexd('B'), Co.hexd('C'), Co.hexd('D'), Co.hexd('E'), Co.hexd('F'), Co.hexd('/'), Co.hexd(':'), Co.hexd('@'), Co.hexd('G'), Co.hexd('`'), Co.hexd('g'), Co.hexd('#'), Co.hexd(' ')] == [Some{0}, Some{1}, Some{2}, Some{3}, Some{4}, Some{5}, Some{6}, Some{7}, Some{8}, Some{9}, Some{10}, Some{11}, Some{12}, Some{13}, Some{14}, Some{15}, Some{10}, Some{11}, Some{12}, Some{13}, Some{14}, Some{15}, None{}, None{}, None{}, None{}, None{}, None{}, None{}, None{}] : List<&2, Maybe<&2, U32>>}

# LAW R1 #rrggbb reads as its three channels, each the high digit times 16
# plus the low digit, in the order written
# EXCLUDES: a wrong digit weight, swapped digits or channels
law theme_hex_value:
  for +a1: Char
  for +a2: Char
  for +a3: Char
  for +a4: Char
  for +a5: Char
  for +a6: Char
  for +x1: U32
  for +x2: U32
  for +x3: U32
  for +x4: U32
  for +x5: U32
  for +x6: U32
  for h1: {Co.hexd(a1) == Some{x1} : Maybe<&2, U32>}
  for h2: {Co.hexd(a2) == Some{x2} : Maybe<&2, U32>}
  for h3: {Co.hexd(a3) == Some{x3} : Maybe<&2, U32>}
  for h4: {Co.hexd(a4) == Some{x4} : Maybe<&2, U32>}
  for h5: {Co.hexd(a5) == Some{x5} : Maybe<&2, U32>}
  for h6: {Co.hexd(a6) == Some{x6} : Maybe<&2, U32>}
  {Co.hex(SCon{'#', SCon{a1, SCon{a2, SCon{a3, SCon{a4, SCon{a5, SCon{a6, SNil{}}}}}}}}) == Some{Co.Rgb{(x1 * 16 + x2 : U32), (x3 * 16 + x4 : U32), (x5 * 16 + x6 : U32)}} : Maybe<&2, Co.Rgb>}

# LAW R1 a color is read only from seven characters, the first a #
# EXCLUDES: reading a prefix of a longer text, or text without the #
law theme_hex_shape:
  for +s: String
  for +c: Co.Rgb
  for h: {Co.hex(s) == Some{c} : Maybe<&2, Co.Rgb>}
  {th.sharp7(s) == True{} : Bool}

# LAW R1 every index 0-255, written in decimal, reads back
# EXCLUDES: a wrong digit value, a lost index
law theme_num_bytes:
  {th.nums(128n, 0) == True{} : Bool}

# LAW R1 every index 128-255, written in decimal, reads back (two laws:
# all 256 at once is past the kernel's fuel)
# EXCLUDES: a wrong digit value, a lost index
law theme_num_bytes_128:
  {th.nums(128n, 128) == True{} : Bool}

# LAW R1 no other number is an index: past 255, signed, fractional,
# leading zeros, empty
# EXCLUDES: wrapping 256 to 0, reading a sign, a fraction or an exponent
law theme_num_example:
  {[Co.num("256"), Co.num("-1"), Co.num("1.5"), Co.num("007"), Co.num(""), Co.num("1000"), Co.num("1e2"), Co.num("255"), Co.num("0")] == [None{}, None{}, None{}, None{}, None{}, None{}, None{}, Some{255}, Some{0}] : List<&2, Maybe<&2, U32>>}

# LAW the xterm-256 cube and gray colors (16-255) quantize back to their
# own index; four laws of 60 indices each (one is past the kernel's fuel)
# EXCLUDES: a quantization that misses a palette color
law theme_to256_palette_16:
  {th.fixed(60n, 16) == True{} : Bool}

# LAW the palette colors 76-135 quantize back to their own index
# EXCLUDES: a quantization that misses a palette color
law theme_to256_palette_76:
  {th.fixed(60n, 76) == True{} : Bool}

# LAW the palette colors 136-195 quantize back to their own index
# EXCLUDES: a quantization that misses a palette color
law theme_to256_palette_136:
  {th.fixed(60n, 136) == True{} : Bool}

# LAW the palette colors 196-255 quantize back to their own index
# EXCLUDES: a quantization that misses a palette color
law theme_to256_palette_196:
  {th.fixed(60n, 196) == True{} : Bool}

# LAW the WCAG contrast at its extremes: black on white clears 4.5:1, white
# on black 3:1, a color on itself not even 3:1
# EXCLUDES: a contrast that depends on the order of the pair, or that
#   always passes
law theme_contrast_example:
  {[Co.contrast_ge(Co.Rgb{0, 0, 0}, Co.Rgb{255, 255, 255}, 9, 2), Co.contrast_ge(Co.Rgb{255, 255, 255}, Co.Rgb{0, 0, 0}, 3, 1), Co.contrast_ge(Co.Rgb{255, 255, 255}, Co.Rgb{255, 255, 255}, 3, 1)] == [True{}, True{}, False{}] : List<&2, Bool>}

# Values

# LAW R1 R2 a value resolves as the rule says, for every variables and
# value
# EXCLUDES: a chain followed too far or not far enough, a cycle or a
#   missing variable reported as another error or with another name, a
#   malformed color read as a default
law theme_chase_rule:
  for +vars: List<&2, T.Var>
  for +j: T.Json
  {T.chase(vars, j) == th.chase(vars, j) : T.Got}

def th.vs() -> List<&2, T.Var>:
  [T.Var{"a", T.JStr{"b", Some{1n}}}, T.Var{"b", T.JStr{"#102030", None{}}}, T.Var{"c", T.JStr{"c", Some{2n}}}, T.Var{"d", T.JStr{"e", Some{4n}}}, T.Var{"e", T.JStr{"d", Some{3n}}}, T.Var{"f", T.JStr{"d", Some{3n}}}]

# LAW R1 R2 anchors: a chain to a hex color, a self-cycle, a cycle entered
# from a tail (it names where the chain closes), a missing variable, the
# terminal default, an index, malformed values
# EXCLUDES: a rule that names the start of the chain for a cycle, or
#   reports any of these as another error
law theme_chase_example:
  {[T.chase(th.vs(), T.JStr{"a", Some{0n}}), T.chase(th.vs(), T.JStr{"c", Some{2n}}), T.chase(th.vs(), T.JStr{"f", Some{5n}}), T.chase(th.vs(), T.JStr{"zz", None{}}), T.chase(th.vs(), T.JStr{"", None{}}), T.chase(th.vs(), T.JNum{"7"}), T.chase(th.vs(), T.JNum{"300"}), T.chase(th.vs(), T.JStr{"#12345", None{}}), T.chase(th.vs(), T.JOther{"null"})] == [T.Hit{T.Hex{Co.Rgb{16, 32, 48}}}, T.Miss{T.Circular{"c"}}, T.Miss{T.Circular{"d"}}, T.Miss{T.NotFound{"zz"}}, T.Hit{T.Dflt{}}, T.Hit{T.Idx{7}}, T.Miss{T.BadValue{"300"}}, T.Miss{T.BadHex{"#12345"}}, T.Miss{T.BadValue{"null"}}] : List<&2, T.Got>}

# Reading a file

# LAW R3 a color key that names no token is that error
# EXCLUDES: skipping an unknown key
law theme_entry_unknown:
  for +vars: List<&2, T.Var>
  for +k: String
  for +j: T.Json
  {T.entry(vars, T.REnt{k, None{}, j}) == T.Bad{T.Unknown{k}} : T.EntR}

# LAW R3 a token's color is its value resolved
# EXCLUDES: a color stored under another token or with another value
law theme_entry_color:
  for +vars: List<&2, T.Var>
  for +k: String
  for +t: U32
  for +j: T.Json
  for +v: T.Val
  for h: {T.chase(vars, j) == T.Hit{v} : T.Got}
  {T.entry(vars, T.REnt{k, Some{t}, j}) == T.Good{T.Ent{t, v}} : T.EntR}

# LAW R3 a token whose value is no color is that error, under its key
# EXCLUDES: an error that loses its key or its cause
law theme_entry_invalid:
  for +vars: List<&2, T.Var>
  for +k: String
  for +t: U32
  for +j: T.Json
  for +why: T.Why
  for h: {T.chase(vars, j) == T.Miss{why} : T.Got}
  {T.entry(vars, T.REnt{k, Some{t}, j}) == T.Bad{T.InColor{k, why}} : T.EntR}

# LAW R3 a file reports the error of its first color (in key order) that
# does not read, whatever follows
# EXCLUDES: reporting a later error first, or a missing token before a
#   color error
law theme_read_first_error:
  for +nm: String
  for +vars: List<&2, T.Var>
  for +pre: List<&2, T.REnt>
  for +e: T.REnt
  for +post: List<&2, T.REnt>
  for +pg: Maybe<&2, T.Json>
  for +cd: Maybe<&2, T.Json>
  for +io: Maybe<&2, T.Json>
  for +f: T.Fault
  for ok: {th.clean(vars, pre) == True{} : Bool}
  for bad: {T.entry(vars, e) == T.Bad{f} : T.EntR}
  {T.read(T.RFile{nm, vars, List.append(&2, T.REnt, pre, e <> post), pg, cd, io}) == T.Failed{f} : T.Read}

# LAW R3 the model's required tokens are the documented ones
# EXCLUDES: a token made optional or required by mistake
law theme_required_tokens:
  {th.reqs(T.toks()) == th.required() : List<&2, U32>}

# LAW R3 a file whose colors read reports every required token it does
# not write, in token order
# EXCLUDES: reporting only the first missing token, a wrong order, an
#   export error before the missing tokens
law theme_read_missing:
  for +nm: String
  for +vars: List<&2, T.Var>
  for +cols: List<&2, T.REnt>
  for +pg: Maybe<&2, T.Json>
  for +cd: Maybe<&2, T.Json>
  for +io: Maybe<&2, T.Json>
  for +t: U32
  for +ts: List<&2, U32>
  for ok: {th.clean(vars, cols) == True{} : Bool}
  for miss: {th.absent(th.goods(vars, cols)) == t <> ts : List<&2, U32>}
  {T.read(T.RFile{nm, vars, cols, pg, cd, io}) == T.Failed{T.Missing{t <> ts}} : T.Read}

# LAW R3 then an export page that is no color is that error
# EXCLUDES: ignoring a broken export background
law theme_read_page:
  for +nm: String
  for +vars: List<&2, T.Var>
  for +cols: List<&2, T.REnt>
  for +j: T.Json
  for +cd: Maybe<&2, T.Json>
  for +io: Maybe<&2, T.Json>
  for +why: T.Why
  for ok: {th.clean(vars, cols) == True{} : Bool}
  for all: {th.absent(th.goods(vars, cols)) == [] : List<&2, U32>}
  for bad: {T.chase(vars, j) == T.Miss{why} : T.Got}
  {T.read(T.RFile{nm, vars, cols, Some{j}, cd, io}) == T.Failed{T.InExport{T.OnPage{}, why}} : T.Read}

# LAW R3 then an export card that is no color
# EXCLUDES: checking the card before the page, or not at all
law theme_read_card:
  for +nm: String
  for +vars: List<&2, T.Var>
  for +cols: List<&2, T.REnt>
  for +pg: Maybe<&2, T.Json>
  for +j: T.Json
  for +io: Maybe<&2, T.Json>
  for +why: T.Why
  for ok: {th.clean(vars, cols) == True{} : Bool}
  for all: {th.absent(th.goods(vars, cols)) == [] : List<&2, U32>}
  for fine: {th.fine(vars, pg) == True{} : Bool}
  for bad: {T.chase(vars, j) == T.Miss{why} : T.Got}
  {T.read(T.RFile{nm, vars, cols, pg, Some{j}, io}) == T.Failed{T.InExport{T.OnCard{}, why}} : T.Read}

# LAW R3 then an export info background that is no color
# EXCLUDES: checking the info background early, or not at all
law theme_read_info:
  for +nm: String
  for +vars: List<&2, T.Var>
  for +cols: List<&2, T.REnt>
  for +pg: Maybe<&2, T.Json>
  for +cd: Maybe<&2, T.Json>
  for +j: T.Json
  for +why: T.Why
  for ok: {th.clean(vars, cols) == True{} : Bool}
  for all: {th.absent(th.goods(vars, cols)) == [] : List<&2, U32>}
  for fine1: {th.fine(vars, pg) == True{} : Bool}
  for fine2: {th.fine(vars, cd) == True{} : Bool}
  for bad: {T.chase(vars, j) == T.Miss{why} : T.Got}
  {T.read(T.RFile{nm, vars, cols, pg, cd, Some{j}}) == T.Failed{T.InExport{T.OnInfo{}, why}} : T.Read}

# LAW R3 R4 a file with no error reads to its colors and the export
# colors it sets ("" sets none)
# EXCLUDES: dropping or reordering a color, losing the card or info
#   background, an export "" that sets a color
law theme_read_loaded:
  for +nm: String
  for +vars: List<&2, T.Var>
  for +cols: List<&2, T.REnt>
  for +pg: Maybe<&2, T.Json>
  for +cd: Maybe<&2, T.Json>
  for +io: Maybe<&2, T.Json>
  for ok: {th.clean(vars, cols) == True{} : Bool}
  for all: {th.absent(th.goods(vars, cols)) == [] : List<&2, U32>}
  for fine1: {th.fine(vars, pg) == True{} : Bool}
  for fine2: {th.fine(vars, cd) == True{} : Bool}
  for fine3: {th.fine(vars, io) == True{} : Bool}
  {T.read(T.RFile{nm, vars, cols, pg, cd, io}) == T.Loaded{T.Th{nm, th.goods(vars, cols), th.bgv(vars, pg), th.bgv(vars, cd), th.bgv(vars, io)}} : T.Read}

# Completion

# LAW R3 a file that does not read is rejected with its error
# EXCLUDES: a palette for a broken file, a changed error
law theme_parse_rejected:
  for +f: T.RFile
  for +x: T.Fault
  for h: {T.read(f) == T.Failed{x} : T.Read}
  {T.parse(f) == T.Rejected{x} : T.Parsed}

# LAW R4 a file that reads gives its palette, its mode, its own #rrggbb
# background and its export backgrounds
# EXCLUDES: a palette, mode or export color of another file, a declared
#   background from an index
law theme_parse_painted:
  for +f: T.RFile
  for +nm: String
  for +cols: List<&2, T.Ent>
  for +pg: Maybe<&2, Co.Rgb>
  for +cd: Maybe<&2, Co.Rgb>
  for +io: Maybe<&2, Co.Rgb>
  for h: {T.read(f) == T.Loaded{T.Th{nm, cols, pg, cd, io}} : T.Read}
  {T.parse(f) == T.Painted{T.vals(T.palette(T.Th{nm, cols, pg, cd, io})), T.light(T.Th{nm, cols, pg, cd, io}), th.own(T.get(cols, 57)), pg, cd, io} : T.Parsed}

# LAW R4 the palette fills every token in token order
# EXCLUDES: a palette in another order, or that skips a token
law theme_palette_tokens:
  for +nm: String
  for +cols: List<&2, T.Ent>
  for +pg: Maybe<&2, Co.Rgb>
  for +cd: Maybe<&2, Co.Rgb>
  for +io: Maybe<&2, Co.Rgb>
  {T.palette(T.Th{nm, cols, pg, cd, io}) == T.fill.map(cols, T.background(cols, pg), T.toks()) : List<&2, Maybe<&2, T.Val>>}

# LAW R4 a required token keeps the value the file writes
# EXCLUDES: a written color replaced by a default
law theme_fill_required:
  for +cols: List<&2, T.Ent>
  for +bg: Co.Rgb
  for +t: U32
  for r: {T.required(t) == True{} : Bool}
  {T.fill(cols, bg, t) == T.get(cols, t) : Maybe<&2, T.Val>}

# LAW R4 mdBody is its own value, else text's
# EXCLUDES: mdBody without a fallback, or text overriding mdBody
law theme_fill_md:
  for +cols: List<&2, T.Ent>
  for +bg: Co.Rgb
  {T.fill(cols, bg, 18) == T.or(T.Val, T.get(cols, 18), T.get(cols, 9)) : Maybe<&2, T.Val>}

# LAW R4 the refinement pair is its own value, else the builtin of the
# background's mode
# EXCLUDES: a dark default on a light theme, a default over a written value
law theme_fill_refinement:
  for +cols: List<&2, T.Ent>
  for +bg: Co.Rgb
  {[T.fill(cols, bg, 14), T.fill(cols, bg, 15)] == [Some{T.or_else(T.Val, T.get(cols, 14), T.Hex{T.at(T.defaults(Co.light(bg)), 14n)})}, Some{T.or_else(T.Val, T.get(cols, 15), T.Hex{T.at(T.defaults(Co.light(bg)), 15n)})}] : List<&2, Maybe<&2, T.Val>>}

# LAW R4 the background token paints the background; the foreground is
# the file's own color, else the builtin of the background's mode
# EXCLUDES: a terminal default left in the canvas tokens
law theme_fill_canvas:
  for +cols: List<&2, T.Ent>
  for +bg: Co.Rgb
  {[T.fill(cols, bg, 57), T.fill(cols, bg, 58)] == [Some{T.Hex{bg}}, Some{T.Hex{T.or_else(Co.Rgb, T.concrete.of(T.get(cols, 58)), T.at(T.defaults(Co.light(bg)), 58n))}}] : List<&2, Maybe<&2, T.Val>>}

# LAW R4 the builtins whose values fill a file: the default theme for a
# dark background, light for a light one
# EXCLUDES: fallbacks from the wrong builtin
law theme_defaults_shipped:
  {[T.defaults(False{}), T.defaults(True{})] == [T.table(T.Eukhe{}), T.table(T.Light{})] : List<&2, List<&2, Co.Rgb>>}

# LAW R4 the background is the file's own color, else its export page,
# else its user-message surface, else the default theme's background
# EXCLUDES: another order of the fallbacks, a default over a written color
law theme_background_order:
  for +cols: List<&2, T.Ent>
  for +pg: Maybe<&2, Co.Rgb>
  {T.background(cols, pg) == T.or_else(Co.Rgb, T.or(Co.Rgb, T.concrete.of(T.get(cols, 57)), T.or(Co.Rgb, pg, T.concrete.of(T.get(cols, 49)))), T.at(T.table(T.Eukhe{}), 57n)) : Co.Rgb}

# Picking a theme

# LAW R5 the theme a name picks is the resolution over the files that
# load: the registered ones, the builtins, the custom ones
# EXCLUDES: a file that did not load picked, a custom file before a
#   registered one, a file id that is not its index after the builtins
law theme_pick_res:
  for +ls: List<&2, T.Ld>
  for +n: String
  {th.res(T.pick(ls, n)) == th.pick(ls, n) : T.Res}

# LAW R5 a name that picks no theme warns with the first file that blames
# it, else with "not found"
# EXCLUDES: a cause from a later file, a cause that is not the name's
law theme_pick_cause:
  for +ls: List<&2, T.Ld>
  for +n: String
  for +id: U32
  for w: {th.pick(ls, n) == T.Res{id, True{}} : T.Res}
  {th.cause(T.pick(ls, n)) == Some{th.cause.of(th.blame(ls, n, 0n))} : Maybe<&2, T.Cause>}

# LAW R5 a name that picks a theme warns with no cause
# EXCLUDES: a cause reported for a resolved name
law theme_pick_quiet:
  for +ls: List<&2, T.Ld>
  for +n: String
  for +id: U32
  for w: {th.pick(ls, n) == T.Res{id, False{}} : T.Res}
  {th.cause(T.pick(ls, n)) == None{} : Maybe<&2, T.Cause>}

# LAW R5 every file that did not load warns once: in the cause, or in the
# broken list, in file order
# EXCLUDES: a lost or doubled failure
law theme_pick_broken:
  for +ls: List<&2, T.Ld>
  for +n: String
  for +id: U32
  for +w: Bool
  for r: {th.pick(ls, n) == T.Res{id, w} : T.Res}
  {th.broken.of(T.pick(ls, n)) == th.broken(ls, th.skip(w, th.blame(ls, n, 0n)), 0n) : List<&2, Nat>}

# LAW R5 the clashes: every loaded file whose name an earlier loaded file
# has first, with that file, in file order
# EXCLUDES: a lost clash, a clash with the wrong file
law theme_pick_clashes:
  for +ls: List<&2, T.Ld>
  for +n: String
  {th.clashes.of(T.pick(ls, n)) == th.clashes(ls) : List<&2, T.Clash>}

def th.ls() -> List<&2, T.Ld>:
  [T.Fine{"dusk", False{}}, T.Broke{Some{"mist"}, Some{"a"}}, T.Broke{None{}, Some{"mist"}}, T.Fine{"dusk", True{}}]

# LAW R5 anchor: a registered "dusk" shadows a custom one (a clash), a
# broken file named "mist" is the cause for "mist"
# EXCLUDES: a reading of the laws above that the human did not mean
law theme_pick_example:
  {[T.pick(th.ls(), "dusk"), T.pick(th.ls(), "mist")] == [T.Pick{T.Res{3, False{}}, None{}, [T.Clash{3n, 0n}], [1n, 2n]}, T.Pick{T.Res{0, True{}}, Some{T.FailedAt{1n}}, [T.Clash{3n, 0n}], [2n]}] : List<&2, T.Pick>}

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

# The recovery Rust calls (decide.rs `recover`, through the compiled
# core) is decide.recover of bend/run.bend: the recoveries above (Rec.go)
# reading the stuck reply and the note's row as Rust has them. The
# helpers rust.* are `recover` as decide.rs wrote it: the row of each
# recovery that the request's note counts (`NoteCause::row`), its cap,
# and the rounds in a row of calls against REPEAT_CALLS.

# the length notes, leak notes and redirect notes in a row that a note of
# recovery k with row `row` makes
def rust.long_row(k: Rn.Rk, row: Nat) -> Nat:
  match k:
    case Rn.Free{}:
      0n
    case Rn.Longs{}:
      row
    case Rn.Leaks{}:
      0n
    case Rn.Loops{}:
      0n

def rust.leak_row(k: Rn.Rk, row: Nat) -> Nat:
  match k:
    case Rn.Free{}:
      0n
    case Rn.Longs{}:
      0n
    case Rn.Leaks{}:
      row
    case Rn.Loops{}:
      0n

def rust.loop_row(k: Rn.Rk, row: Nat) -> Nat:
  match k:
    case Rn.Free{}:
      0n
    case Rn.Longs{}:
      0n
    case Rn.Leaks{}:
      0n
    case Rn.Loops{}:
      row

# under the cap a retry with the next note of the recovery; at it, cap
def rust.redo(under: Bool, row: Nat, cap: Rn.Help) -> Rn.Help:
  match under:
    case True{}:
      Rn.Redoes{1n+row}
    case False{}:
      cap

# calls below REPEAT_CALLS rounds in a row run; else the other act
def rust.calls(fresh: Bool, other: Rn.Help) -> Rn.Help:
  match fresh:
    case True{}:
      Rn.Runs{}
    case False{}:
      other

# `recover`
def rust.recover(rc: Rn.RCfg, s: Rn.Stuck, +k: Rn.Rk, +row: Nat) -> Rn.Help:
  match rc:
    case Rn.RCfg{long, leak, redirect, repeat}:
      match s:
        case Rn.Truncated{}:
          rust.redo(Nat.is_lt(rust.long_row(k, row), long), rust.long_row(k, row), Rn.Quits{})
        case Rn.Leaked{}:
          rust.redo(Nat.is_lt(rust.leak_row(k, row), leak), rust.leak_row(k, row), Rn.Stands{})
        case Rn.Repeats{before}:
          rust.calls(Nat.is_lt(1n+before, repeat), rust.redo(Nat.is_lt(rust.loop_row(k, row), redirect), rust.loop_row(k, row), Rn.Quits{}))

# LAW: what a recovery does with any stuck reply, after any note, under
# any caps, is what `recover` did: the code that runs is the recoveries
# whose laws are above
law rec_recover_is_the_rust_rule:
  for +rc: Rn.RCfg
  for +s: Rn.Stuck
  for +k: Rn.Rk
  for +row: Nat
  {Rn.decide.recover(rc, s, k, row) == rust.recover(rc, s, k, row) : Rn.Help}

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
# tests crates/eukhe-daemon/src/supervision_bridge.rs and
# crates/eukhe-tui/src/restore_notices.rs run the Rust code and each
# model on the same scenarios; the replacement verdict runs as its model
# (the compiled core, section `replace: the entry`). Every input is free: any configuration, any
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

# the ages a failure g ms after the last one keeps (each g ms older), in
# order: those still inside the window of w ms
def restart_window_put(b: Bool, a: Nat, r: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case True{}:
      a <> r
    case False{}:
      r

def restart_window(+w: Nat, +g: Nat, ages: List<&2, Nat>) -> List<&2, Nat>:
  match ages:
    case Nil{}:
      Nil{}
    case +a <> t:
      restart_window_put(Nat.is_lt(Nat.add(g, a), w), Nat.add(g, a), restart_window(w, g, t))

# 2 to the e
def restart_pow2(e: Nat) -> Nat:
  match e:
    case 0n:
      1n
    case 1n+p:
      Nat.mul(2n, restart_pow2(p))

# the verdict on the n-th failure in the window: past k failures the
# worker is given up; else it relaunches after base * 2^min(n - 1, 7) ms,
# at most max ms
def restart_verdict_put(over: Bool, +c: Su.Cfg, +n: Nat) -> Su.Verdict:
  match over:
    case True{}:
      Su.GiveUp{n}
    case False{}:
      match c:
        case Su.Cfg{k, w, b, m}:
          Su.Relaunch{n, Nat.min(Nat.mul(restart_pow2(Nat.min(Nat.sub(n, 1n), 7n)), b), m)}

# LAW: a failure keeps exactly the ages still inside the window (each one
# g ms older, in order), adds itself at age 0 in front, and counts the
# failures it keeps
# EXCLUDES: a dropped young failure, a kept old one, a failure counted
# twice or not at all, a reordered history, an age that does not grow
law restart_decide_window:
  for +c: Su.Cfg
  for +s: Su.St
  for +g: Nat
  {Su.Decision.st(Su.decide(c, s, g)) == Su.St{0n <> restart_window(Su.Cfg.w(c), g, Su.St.ages(s)), 1n+List.length(&2, Nat, restart_window(Su.Cfg.w(c), g, Su.St.ages(s)))} : Su.St}

# LAW: the verdict on a failure: give up past k failures in the window,
# else relaunch after the doubling pause, capped at max
# EXCLUDES: a give-up at k failures or a relaunch past them, a wrong
# failure count, a pause that does not double, passes its cap or doubles
# past 7 times
law restart_decide_verdict:
  for +c: Su.Cfg
  for +s: Su.St
  for +g: Nat
  {Su.Decision.verdict(Su.decide(c, s, g)) == restart_verdict_put(Nat.is_lt(Su.Cfg.k(c), 1n+List.length(&2, Nat, restart_window(Su.Cfg.w(c), g, Su.St.ages(s)))), c, 1n+List.length(&2, Nat, restart_window(Su.Cfg.w(c), g, Su.St.ages(s)))) : Su.Verdict}

# The restart-budget entry of the compiled core (bend/ffi_supervise.bend)

# LAW: the entry reads back every request Rust writes: a configuration,
# ages and a gap that fit the wire; the rest is untouched
# EXCLUDES: a misread or reordered configuration field, age or gap
law restart_wire_req:
  for +k: Nat
  for hk: {wire_fits(k) == True{} : Bool}
  for +w: Nat
  for hw: {wire_fits(w) == True{} : Bool}
  for +b: Nat
  for hb: {wire_fits(b) == True{} : Bool}
  for +m: Nat
  for hm: {wire_fits(m) == True{} : Bool}
  for +ages: List<&2, Nat>
  for hs: {Bool.and(wire_fits(List.length(&2, Nat, ages)), wire_nats_fit(ages)) == True{} : Bool}
  for +g: Nat
  for hg: {wire_fits(g) == True{} : Bool}
  for rest: String
  {FS.get_req(FS.put_req(FS.Req{Su.Cfg{k, w, b, m}, ages, g}, rest)) == Wr.Got{FS.Req{Su.Cfg{k, w, b, m}, ages, g}, rest} : Wr.Dec<FS.Req>}

# LAW: Rust reads back every relaunch reply the entry writes
# EXCLUDES: a misread age, failure count or pause, a verdict read as another
law restart_wire_reply_relaunch:
  for +ages: List<&2, Nat>
  for hs: {Bool.and(wire_fits(List.length(&2, Nat, ages)), wire_nats_fit(ages)) == True{} : Bool}
  for +f: Nat
  for hf: {wire_fits(f) == True{} : Bool}
  for +p: Nat
  for hp: {wire_fits(p) == True{} : Bool}
  for rest: String
  {FS.get_reply(FS.put_reply(FS.Reply{ages, Su.Relaunch{f, p}}, rest)) == Wr.Got{FS.Reply{ages, Su.Relaunch{f, p}}, rest} : Wr.Dec<FS.Reply>}

# LAW: and every give-up reply
# EXCLUDES: a give-up read as a relaunch, a misread failure count
law restart_wire_reply_give_up:
  for +ages: List<&2, Nat>
  for hs: {Bool.and(wire_fits(List.length(&2, Nat, ages)), wire_nats_fit(ages)) == True{} : Bool}
  for +f: Nat
  for hf: {wire_fits(f) == True{} : Bool}
  for rest: String
  {FS.get_reply(FS.put_reply(FS.Reply{ages, Su.GiveUp{f}}, rest)) == Wr.Got{FS.Reply{ages, Su.GiveUp{f}}, rest} : Wr.Dec<FS.Reply>}

# LAW: on a whole request the entry answers the model's decision: the
# budget's new ages and the verdict (Su.decide)
# EXCLUDES: an entry that answers anything but the model's decision
law restart_ffi_decides:
  for +s: String
  for +c: Su.Cfg
  for +ages: List<&2, Nat>
  for +g: Nat
  for h: {FS.get_req(s) == Wr.Got{FS.Req{c, ages, g}, ""} : Wr.Dec<FS.Req>}
  {FS.ffi(s) == FS.put_reply(FS.Reply{Su.St.ages(Su.Decision.st(Su.decide(c, Su.St{ages, List.length(&2, Nat, ages)}, g))), Su.Decision.verdict(Su.decide(c, Su.St{ages, List.length(&2, Nat, ages)}, g))}, "") : String}

# LAW: a malformed request answers the error form, never a verdict
# EXCLUDES: a default verdict on garbage
law restart_ffi_malformed:
  for +s: String
  for h: {FS.get_req(s) == Wr.Bad{} : Wr.Dec<FS.Req>}
  {FS.ffi(s) == Wr.err("supervise: malformed request") : String}

# LAW: a request with input after it answers the error form
# EXCLUDES: a verdict on a request with trailing garbage
law restart_ffi_left_over:
  for +s: String
  for +q: FS.Req
  for +r: String
  for h: {FS.get_req(s) == Wr.Got{q, r} : Wr.Dec<FS.Req>}
  for ne: {String.is_empty(r) == False{} : Bool}
  {FS.ffi(s) == Wr.err("supervise: input left over") : String}

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

# LAW: an orphaned worker without work exits once the whole window passed
# (any window, any absence)
# EXCLUDES: an exit before the window, a worker kept alive past it
law orphan_idle_exit_due:
  for +window: Nat
  for +absent: Nat
  {Or.exit_due.at(Some{window}, absent, Or.Idle{}) == Nat.is_le(window, absent) : Bool}

# LAW: an orphaned worker with work exits once two windows passed: the
# work defers the exit by exactly one more window, never forever
# EXCLUDES: work that does not defer the exit, defers it forever, or by
# a wrong amount
law orphan_work_exit_due:
  for +window: Nat
  for +absent: Nat
  {Or.exit_due.at(Some{window}, absent, Or.Ongoing{}) == Nat.is_le(Nat.add(window, window), absent) : Bool}

# LAW: a window past the runtime's Nat range (Rust saturates a larger env
# window to `None`) never expires, whatever the absence and the work
# EXCLUDES: a saturated huge window that turns into an early exit
law orphan_capped_window_never_expires:
  for +absent: Nat
  for work: Or.Work
  {Or.exit_due.at(None{}, absent, work) == False{} : Bool}

def orphan_exit_spec(work: Or.Work) -> Or.Exit:
  match work:
    case Or.Idle{}:
      Or.Shut{}
    case Or.Ongoing{}:
      Or.Handover{}

# LAW: without work the orphan exit closes the session; with work it
# hands the work over (both values of Work)
# EXCLUDES: a handover of nothing, a close that drops work
law orphan_exit_by_work:
  for work: Or.Work
  {Or.orphan_exit(work) == orphan_exit_spec(work) : Or.Exit}

# The orphan entry of the compiled core (bend/ffi_orphan.bend)

# LAW: the entry reads back every request Rust writes: a window that fits
# the wire, an absence that fits, the work; the rest is untouched
# EXCLUDES: a misread window, absence or work, a lost or eaten rest
law orphan_wire_req_window:
  for +w: Nat
  for hw: {wire_fits(w) == True{} : Bool}
  for +a: Nat
  for ha: {wire_fits(a) == True{} : Bool}
  for +k: Or.Work
  for rest: String
  {FO.get_req(FO.put_req(FO.Req{Some{w}, a, k}, rest)) == Wr.Got{FO.Req{Some{w}, a, k}, rest} : Wr.Dec<FO.Req>}

# LAW: and a request with no window (past the wire's range)
# EXCLUDES: a missing window read as some window
law orphan_wire_req_no_window:
  for +a: Nat
  for ha: {wire_fits(a) == True{} : Bool}
  for +k: Or.Work
  for rest: String
  {FO.get_req(FO.put_req(FO.Req{None{}, a, k}, rest)) == Wr.Got{FO.Req{None{}, a, k}, rest} : Wr.Dec<FO.Req>}

# LAW: Rust reads back every reply the entry writes
# EXCLUDES: a swapped due flag or exit
law orphan_wire_reply:
  for +d: Bool
  for +e: Or.Exit
  for rest: String
  {FO.get_reply(FO.put_reply(FO.Reply{d, e}, rest)) == Wr.Got{FO.Reply{d, e}, rest} : Wr.Dec<FO.Reply>}

# LAW: on a whole request the entry answers the model's decision: whether
# the worker exits now, and how
# EXCLUDES: an entry that answers anything but exit_due.at and orphan_exit
law orphan_ffi_decides:
  for +s: String
  for +m: Maybe<&2, Nat>
  for +a: Nat
  for +k: Or.Work
  for h: {FO.get_req(s) == Wr.Got{FO.Req{m, a, k}, ""} : Wr.Dec<FO.Req>}
  {FO.ffi(s) == FO.put_reply(FO.Reply{Or.exit_due.at(m, a, k), Or.orphan_exit(k)}, "") : String}

# LAW: a malformed request answers the error form, never a decision
# EXCLUDES: a default decision on garbage
law orphan_ffi_malformed:
  for +s: String
  for h: {FO.get_req(s) == Wr.Bad{} : Wr.Dec<FO.Req>}
  {FO.ffi(s) == Wr.err("orphan: malformed request") : String}

# LAW: a request with input after it answers the error form
# EXCLUDES: a decision on a request with trailing garbage
law orphan_ffi_left_over:
  for +s: String
  for +q: FO.Req
  for +r: String
  for h: {FO.get_req(s) == Wr.Got{q, r} : Wr.Dec<FO.Req>}
  for ne: {String.is_empty(r) == False{} : Bool}
  {FO.ffi(s) == Wr.err("orphan: input left over") : String}

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

# The rank of a version, read by semver.bend's reader (the spec): the text
# before the first '-' read as a version X.Y.Z (Sv.Ver.parse: decimal
# numbers without leading zeros, three of them, nothing else) whose
# numbers have at most 14 digits; [X, Y, 0, Z] with a '-' (a prerelease),
# [X, Y, 1, Z] without; [] for any other text. A number of 15 digits or
# more is past the range of the compiled core's numbers (2^48 - 1): its
# version has no rank, as text that is no version. A text of more than 64
# chars has no rank either (no version is that long): the first 65 chars
# of any text decide its rank, so Rust sends only those.

def rank_spec.core.at(dash: Bool, c: Char, rest: String) -> String:
  match dash:
    case True{}:
      SNil{}
    case False{}:
      SCon{c, rest}

# the text before the first '-'
def rank_spec.core(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, r}:
      rank_spec.core.at(Char.is_eq(c, '-'), c, rank_spec.core(r))

def rank_spec.tier.at(dash: Bool, rest: Nat) -> Nat:
  match dash:
    case True{}:
      0n
    case False{}:
      rest

# 0 with a '-' in the text, else 1
def rank_spec.tier(s: String) -> Nat:
  match s:
    case SNil{}:
      1n
    case SCon{c, r}:
      rank_spec.tier.at(Char.is_eq(c, '-'), rank_spec.tier(r))

# x is written with at most 14 digits
def rank_spec.short(+x: Nat) -> Bool:
  Nat.is_le(List.length(&2, Sv.Dig, Sv.Num.dec(x)), 14n)

def rank_spec.keep(ok: Bool, a: Nat, b: Nat, t: Nat, c: Nat) -> List<&2, Nat>:
  match ok:
    case True{}:
      [a, b, t, c]
    case False{}:
      Nil{}

def rank_spec.of(m: Maybe<&2, Sv.Ver>, t: Nat) -> List<&2, Nat>:
  match m:
    case None{}:
      Nil{}
    case Some{v}:
      match v:
        case Sv.Ver{+a, +b, +c}:
          rank_spec.keep(Bool.and(rank_spec.short(a), Bool.and(rank_spec.short(b), rank_spec.short(c))), a, b, t, c)

def rank_spec.cap(short: Bool, +s: String) -> List<&2, Nat>:
  match short:
    case True{}:
      rank_spec.of(Sv.Ver.parse(rank_spec.core(s)), rank_spec.tier(s))
    case False{}:
      Nil{}

def rank_spec(+s: String) -> List<&2, Nat>:
  rank_spec.cap(Nat.is_le(String.length(s), 64n), s)

# a rank is empty, or four numbers whose version numbers (the first, the
# second and the fourth) have at most 14 digits
def rank_spec.in_range(xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case a <> r1:
      match r1:
        case Nil{}:
          False{}
        case b <> r2:
          match r2:
            case Nil{}:
              False{}
            case t <> r3:
              match r3:
                case Nil{}:
                  False{}
                case c <> r4:
                  match r4:
                    case Nil{}:
                      Bool.and(rank_spec.short(a), Bool.and(rank_spec.short(b), rank_spec.short(c)))
                    case e <> r5:
                      False{}

# The order of ranks: lexicographic, the empty rank lowest
def rank_below(xs: List<&2, Nat>, ys: List<&2, Nat>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      False{}
    case Nil{} y <> yr:
      True{}
    case x <> xr Nil{}:
      False{}
    case +x <> xr +y <> yr:
      Bool.or(Nat.is_lt(x, y), Bool.and(Nat.is_eq(x, y), rank_below(xr, yr)))

def rel_spec.pick(same: Bool, older: Bool, newer: Bool) -> Rp.Rel:
  match same older newer:
    case True{} _ _:
      Rp.Same{}
    case False{} True{} _:
      Rp.Older{}
    case False{} False{} True{}:
      Rp.Newer{}
    case False{} False{} False{}:
      Rp.Other{}

# how daemon d relates to client c: the same build id is the same build;
# else the daemon's rank is below (older), above (newer) or neither
# (another build of an equal rank)
def rel_spec(c: Rp.Build, d: Rp.Build) -> Rp.Rel:
  match c d:
    case Rp.Build{+rc, ic} Rp.Build{+rd, id}:
      rel_spec.pick(String.eq(ic, id), rank_below(rd, rc), rank_below(rc, rd))

# an interactive start replaces an older daemon; every other start keeps
# the daemon and names the relation
def verdict_spec(r: Rp.Rel, k: Rp.Caller) -> Rp.Verdict:
  match r k:
    case Rp.Older{} Rp.Interactive{}:
      Rp.Replace{}
    case Rp.Older{} Rp.Background{}:
      Rp.Keep{Rp.Older{}}
    case Rp.Same{} _:
      Rp.Keep{Rp.Same{}}
    case Rp.Newer{} _:
      Rp.Keep{Rp.Newer{}}
    case Rp.Other{} _:
      Rp.Keep{Rp.Other{}}

# LAW: the rank of every text is the rank semver.bend's reader gives it,
# with numbers of at most 14 digits
# EXCLUDES: a reader that accepts a leading zero, an empty field, two or
# four fields, a sign or any other symbol; a reader that rounds, clamps or
# wraps a number past the range instead of refusing it; a wrong tier
law replace_rank_reads_semver:
  for +s: String
  {Rp.rank(s) == rank_spec(s) : List<&2, Nat>}

# LAW: every rank is empty or four numbers, and each version number in it
# has at most 14 digits: a version number past the range never ranks
# EXCLUDES: a clamped or wrapped number (the order of a hostile version
# would change), a rank of another length
law replace_rank_in_range:
  for +s: String
  {rank_spec.in_range(Rp.rank(s)) == True{} : Bool}

# LAW: the versions of the release history rank as documented
# EXCLUDES: a misread spec: textual instead of numeric order, a prerelease
# above its release, a parse of text that is no version
law replace_rank_example:
  {[Rp.rank("garbage"), Rp.rank("0.9.0-dev"), Rp.rank("0.9.9-main.46"), Rp.rank("0.10.40"), Rp.rank("1.2.3-"), Rp.rank("01.2.3"), Rp.rank("1.2"), Rp.rank("1.2.3.4"), Rp.rank(""), Rp.rank("1..3"), Rp.rank("+1.2.3")] == [[], [0n, 9n, 0n, 0n], [0n, 9n, 0n, 9n], [0n, 10n, 1n, 40n], [1n, 2n, 0n, 3n], [], [], [], [], [], []] : List<&2, List<&2, Nat>>}

# LAW: a number of 15 digits has no rank, in any place
# EXCLUDES: a reader that folds a long field into a Nat (the compiled core
# aborts past 2^48 - 1)
law replace_rank_past_range_example:
  {[Rp.rank("100000000000000.0.0"), Rp.rank("0.100000000000000.0"), Rp.rank("0.0.100000000000000-dev")] == [[], [], []] : List<&2, List<&2, Nat>>}

# LAW: the relation of the daemon to the client is exactly rel_spec
# EXCLUDES: a relation that ignores the build ids, compares ranks the
# wrong way round, or calls an equal rank older or newer
law replace_relation_exact:
  for +c: Rp.Build
  for +d: Rp.Build
  {Rp.relation(c, d) == rel_spec(c, d) : Rp.Rel}

# LAW: the verdict of a start is exactly verdict_spec of the relation
# EXCLUDES: a start that never replaces (an older daemon kept for good), a
# background start that replaces, a replaced newer daemon
law replace_verdict_exact:
  for +c: Rp.Build
  for +d: Rp.Build
  for +k: Rp.Caller
  {Rp.verdict(c, d, k) == verdict_spec(rel_spec(c, d), k) : Rp.Verdict}

# LAW: the ping-pong pair settles on the newer build: an old dashboard
# (0.9.9-main.46) and a new client (0.10.40) by every caller, and a client
# of the daemon's own build
# EXCLUDES: the regression where the two replaced each other forever
law replace_ping_pong_example:
  {[Rp.verdict(Rp.Build.of("0.9.9-main.46", "o"), Rp.Build.of("0.10.40", "n"), Rp.Background{}), Rp.verdict(Rp.Build.of("0.9.9-main.46", "o"), Rp.Build.of("0.10.40", "n"), Rp.Interactive{}), Rp.verdict(Rp.Build.of("0.10.40", "n"), Rp.Build.of("0.9.9-main.46", "o"), Rp.Background{}), Rp.verdict(Rp.Build.of("0.10.40", "n"), Rp.Build.of("0.9.9-main.46", "o"), Rp.Interactive{}), Rp.verdict(Rp.Build.of("0.10.40", "n"), Rp.Build.of("0.10.40", "n"), Rp.Interactive{}), Rp.verdict(Rp.Build.of("0.10.0-dev", "a"), Rp.Build.of("0.10.0-dev", "b"), Rp.Interactive{})] == [Rp.Keep{Rp.Newer{}}, Rp.Keep{Rp.Newer{}}, Rp.Keep{Rp.Older{}}, Rp.Replace{}, Rp.Keep{Rp.Same{}}, Rp.Keep{Rp.Other{}}] : List<&2, Rp.Verdict>}

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

# LAW: tokens at or past the window reach what the full window reaches,
# so the caller may cap the tokens at the window (and at any cap at or
# above the window) without changing the band
# EXCLUDES: a band that changes past the full window (an overflow, a
#   wrap, a fraction above one read as more)
law tui_usage_band_full:
  for +t: Nat
  for +w: Nat
  for +past: {Nat.is_le(w, t) == True{} : Bool}
  {TC.band(t, w) == TC.band(w, w) : Nat}

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

# ---- screen: the entry ----

# LAWS (S8, the compiled core): the interface's rules run as the model of
# bend/screen.bend through the compiled core's entry bend/ffi_screen.bend
# (crates/eukhe-tui: view/ledger.rs, pace.rs, view/stack.rs). The laws of
# the model itself are in the first section, (S8) The interface. Every
# input is free: any transcript, events, pace, rate and heights whose
# numbers fit the wire.

# The compiled core's entry of the interface (bend/ffi_screen.bend): Rust
# writes a request with FSc.put_req and reads the reply; every Nat of a
# request fits the wire (at most 14 digits, wire_fits)

# every Nat of a block fits the wire
def blk_fits(b: Sc.Blk) -> Bool:
  match b:
    case Sc.Blk{i, s, l}:
      Bool.and(wire_fits(i), wire_fits(l))

def blks_fit(bs: List<&2, Sc.Blk>) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case Con{b, t}:
      Bool.and(blk_fits(b), blks_fit(t))

# every Nat of an event fits the wire
def ev_fits(e: Sc.Ev) -> Bool:
  match e:
    case Sc.Open{}:
      True{}
    case Sc.Grow{x, n}:
      Bool.and(wire_fits(x), wire_fits(n))
    case Sc.Fin{x}:
      wire_fits(x)
    case Sc.Flush{}:
      True{}
    case Sc.Resize{w}:
      wire_fits(w)

def evs_fit(es: List<&2, Sc.Ev>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case Con{e, t}:
      Bool.and(ev_fits(e), evs_fit(t))

# every Nat of a transcript fits the wire, its block count too
def tx_fits(t: Sc.Tx) -> Bool:
  match t:
    case Sc.Tx{+bs, n, w}:
      Bool.and(wire_fits(List.length(&2, Sc.Blk, bs)), Bool.and(blks_fit(bs), Bool.and(wire_fits(n), wire_fits(w))))

# LAW: the entry runs a frame's events as the model: the reply to a Run
# request is the transcript Sc.run gives, encoded
# EXCLUDES: an entry that misreads a block, an event or the order of the
# events, that drops or invents an event, or answers another transcript
law screen_ffi_run:
  for +t: Sc.Tx
  for +es: List<&2, Sc.Ev>
  for +ft: {tx_fits(t) == True{} : Bool}
  for +fe: {Bool.and(wire_fits(List.length(&2, Sc.Ev, es)), evs_fit(es)) == True{} : Bool}
  {FSc.ffi(FSc.put_req(FSc.ReqRun{t, es}, "")) == FSc.put_tx(Sc.run(es, t), "") : String}

# LAW: the entry paces a frame as the model: n characters arrive, then a
# frame shows its share
# EXCLUDES: an entry that swaps the minimum and the lag, reads recv and
# shown the wrong way round, or frames before the characters arrive
law screen_ffi_pace:
  for +min: Nat
  for +k: Nat
  for +r: Nat
  for +s: Nat
  for +n: Nat
  for +f: {Bool.and(Bool.and(wire_fits(min), wire_fits(k)), Bool.and(Bool.and(wire_fits(r), wire_fits(s)), wire_fits(n))) == True{} : Bool}
  {FSc.ffi(FSc.put_req(FSc.ReqPace{min, k, Sc.Pace{r, s}, n}, "")) == FSc.put_pace(Sc.pace.run([Sc.Chunk{n}, Sc.Frame{}], min, k, Sc.Pace{r, s}), "") : String}

# LAW: the entry stacks children as the model
# EXCLUDES: an entry that misreads a height, the start row or the rows
law screen_ffi_stack:
  for +hs: List<&2, Nat>
  for +y: Nat
  for +rows: Nat
  for +f: {Bool.and(Bool.and(wire_fits(List.length(&2, Nat, hs)), wire_nats_fit(hs)), Bool.and(wire_fits(y), wire_fits(rows))) == True{} : Bool}
  {FSc.ffi(FSc.put_req(FSc.ReqStack{hs, y, rows}, "")) == Wr.put_list(~Sc.Rect, ~FSc.put_rect, Sc.vstack(hs, y, rows), "") : String}

# LAW: the requests Rust writes, as text: a frame (blocks 5 and 6 live,
# open one, finish 5, flush), a pace frame and a stack, with their replies
# EXCLUDES: a request or reply format other than WIRE.md's (tags, field
# order, counts)
law screen_ffi_example:
  {[FSc.ffi("0,2,5,0,0,6,0,0,7,80,3,0,2,5,3,"), FSc.ffi("1,2,3,0,0,400,"), FSc.ffi("2,3,2,3,4,1,5,")] == ["3,5,2,0,6,0,0,7,0,0,8,80,", "400,100,", "3,1,2,3,2,6,0,"] : List<&2, String>}

# LAW: a malformed request or one with input left over answers the error
# form, never a reply
# EXCLUDES: a default reply to a request the entry could not read
law screen_ffi_refuses_example:
  {[FSc.ffi("7,"), FSc.ffi("2,0,0,0,x"), FSc.ffi("1,2,3,0,0,01,")] == [Wr.err("screen: malformed request"), Wr.err("screen: input left over"), Wr.err("screen: malformed request")] : List<&2, String>}

# The paint decision (inline_term.rs `paint_decision`): Rust runs a
# frame's check and asks the entry with the checks run so far, in order;
# the entry answers the paint, or asks for the next check (the full
# redraw's, then the fresh redraw's), which Rust then builds and runs.
# A frame is the index of the attempt that built it: 0 the frame, 1 its
# full redraw, 2 its fresh redraw. Every check result is free.

# the checks the first k attempts give, in order (at most three)
def screen_paint_checks(ok1: Bool, ok2: Bool, ok3: Bool, k: Nat) -> List<&2, Bool>:
  List.take(&2, Bool, [ok1, ok2, ok3], k)

# whether the paint still needs a check after ks: every check run so far
# failed and fewer than n of them ran
def screen_paint_open.go(n: Nat, ks: List<&2, Bool>) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n+m:
      match ks:
        case Nil{}:
          True{}
        case Con{ok, rest}:
          match ok:
            case True{}:
              False{}
            case False{}:
              screen_paint_open.go(m, rest)

def screen_paint_open(ks: List<&2, Bool>) -> Bool:
  screen_paint_open.go(3n, ks)

# what the entry answers: nothing yet while a check is still needed, else
# the paint
def screen_paint_step(open: Bool, p: Sc.Paint) -> Maybe<&2, Sc.Paint>:
  match open:
    case True{}:
      None{}
    case False{}:
      Some{p}

# LAW: after any number of checks, the entry asks for the next check
# exactly while every check run so far failed (and fewer than three ran),
# and otherwise answers the paint of the first passing check
# (screen_paint_spec, the spec of paint_first_passing_check), whatever
# the checks not yet run would answer
# EXCLUDES: a paint decided before the check it depends on ran; a check
# asked for after the paint is settled (a redraw built for nothing); a
# frame drawn after its check failed; a passing redraw left unused; an
# outcome other than Kept after three failed checks; a wrong frame index
law screen_ffi_paint:
  for +k: Nat
  for +ok1: Bool
  for +ok2: Bool
  for +ok3: Bool
  {FSc.ffi(FSc.put_req(FSc.ReqPaint{screen_paint_checks(ok1, ok2, ok3, k)}, "")) == FSc.put_step(screen_paint_step(screen_paint_open(screen_paint_checks(ok1, ok2, ok3, k)), screen_paint_spec(0n, 1n, 2n, ok1, ok2, ok3)), "") : String}

# LAW: the paint requests Rust writes, as text, with their replies; more
# than three checks is refused
# EXCLUDES: a request or reply format other than WIRE.md's (Bools as T
# and F with no comma, the step tags); a reply to a fourth check
law screen_ffi_paint_example:
  {[FSc.ffi("3,1,T"), FSc.ffi("3,1,F"), FSc.ffi("3,2,FT"), FSc.ffi("3,3,FFT"), FSc.ffi("3,3,FFF"), FSc.ffi("3,4,FFFF")] == ["1,0,F", "0,", "1,1,T", "2,2,", "3,0,", Wr.err("screen: more than three checks")] : List<&2, String>}

# ---- replace: the entry ----

# LAWS (D1, the compiled core): the launcher's replacement verdict runs as
# the model of bend/replace.bend through the compiled core's entry
# bend/ffi_replace.bend (crates/eukhe-tui daemon_build.rs). The laws of the
# model itself are in section supervisor. Every input is free: any
# versions, any build ids, any caller.

# LAW: the first 65 chars of a version decide its rank, so the entry may
# read only those
# EXCLUDES: a cut that changes a rank (a cut below 65 chars, or a rank that
# reads past its 65th char)
law replace_rank_cut:
  for +s: String
  {Rp.rank(String.take(s, 65n)) == Rp.rank(s) : List<&2, Nat>}

# LAW: the entry's relation is the model's relation of the two builds: it
# reads the versions, and the build ids only through their equality
# EXCLUDES: an entry that swaps client and daemon, ignores the ids, or
# misreads a version
law replace_ffi_relation:
  for +c: String
  for +d: String
  for +ic: String
  for +id: String
  for +f: {Bool.and(wire_fits(String.length(c)), wire_fits(String.length(d))) == True{} : Bool}
  {FRp.ffi(FRp.put_req(FRp.ReqRelation{c, d, String.eq(ic, id)}, "")) == FRp.put_rel(Rp.relation(Rp.Build.of(c, ic), Rp.Build.of(d, id)), "") : String}

# LAW: the entry's verdict is the model's verdict of a start
# EXCLUDES: an entry that ignores or swaps the caller
law replace_ffi_verdict:
  for +c: String
  for +d: String
  for +ic: String
  for +id: String
  for +k: Rp.Caller
  for +f: {Bool.and(wire_fits(String.length(c)), wire_fits(String.length(d))) == True{} : Bool}
  {FRp.ffi(FRp.put_req(FRp.ReqVerdict{c, d, String.eq(ic, id), k}, "")) == FRp.put_verdict(Rp.verdict(Rp.Build.of(c, ic), Rp.Build.of(d, id), k), "") : String}

# LAW: the requests Rust writes, as text, with their replies: a new client
# by an interactive start on an older daemon (replace), the same build,
# and a relation to a newer daemon; a malformed request is refused
# EXCLUDES: a request or reply format other than WIRE.md's
law replace_ffi_example:
  {[FRp.ffi("1,7,0.10.4013,0.9.9-main.46F0,"), FRp.ffi("1,7,0.10.407,0.10.40T0,"), FRp.ffi("0,13,0.9.9-main.467,0.10.40F"), FRp.ffi("0,7,0.10.40")] == ["0,", "1,0,", "2,", Wr.err("replace: malformed request")] : List<&2, String>}

# ---- tree_ffi ----

# LAWS (S1, the session tree's entry of the compiled core): the Rust
# journal (crates/eukhe-durable/src/tree/journal.rs) drives the stepper of
# bend/ffi_tree.bend, whose state is the core of bend/tree.bend. The laws
# tree_core_* of section S1 pin the core; these pin the entry: every ask
# Rust writes reads back, a step answers the core's answer and keeps the
# core's next state, and every other input answers the error form.

# every Nat of an op fits the wire
def tree.op_fits(o: Tr.Op) -> Bool:
  match o:
    case Tr.Put{k, p, v}:
      Bool.and(wire_fits(k), Bool.and(wire_fits(p), wire_fits(v)))
    case Tr.Del{k}:
      wire_fits(k)

def tree.ops_fit(ops: List<&2, Tr.Op>) -> Bool:
  match ops:
    case Nil{}:
      True{}
    case o <> rest:
      Bool.and(tree.op_fits(o), tree.ops_fit(rest))

# every Nat of an ask fits the wire, and so does the count of a rewind's
# ops
def tree.ask_fits(q: Tr.Ask) -> Bool:
  match q:
    case Tr.Note{r}:
      match r:
        case Tr.Do{o}:
          tree.op_fits(o)
        case Tr.Rewind{+ops}:
          Bool.and(wire_fits(List.length(&2, Tr.Op, ops)), tree.ops_fit(ops))
    case Tr.Plan{n}:
      wire_fits(n)
    case Tr.Snap{n}:
      wire_fits(n)

# LAW: an ask that fits the wire reads back, and the rest is untouched
# EXCLUDES: a field read into the wrong slot, a lost, added or reordered
#   op of a rewind, a record or an op read as another kind
law tree_ffi_ask_round_trip:
  for q: Tr.Ask
  for +rest: String
  for h: {tree.ask_fits(q) == True{} : Bool}
  {Ft.get_ask(Ft.put_ask(q, rest)) == Wr.Got{q, rest} : Wr.Dec<Tr.Ask>}

# LAW: a step answers the core's answer to the ask and keeps the core's
# next state
# EXCLUDES: an entry that answers anything but the core's decision, or
#   that drops, repeats or reorders a record of the core's journal
law tree_ffi_step:
  for +s: Tr.St
  for +q: Tr.Ask
  for h: {tree.ask_fits(q) == True{} : Bool}
  {Ft.step(Ft.Live{s}, Ft.put_ask(q, "")) == (Ft.Live{Pair.fst(Tr.St, Tr.Ans, Tr.core.step(s, q))}, Ft.put_ans(Pair.snd(Tr.St, Tr.Ans, Tr.core.step(s, q)), "")) : Ft.St & String}

# LAW: malformed input answers the error form and keeps the core
# EXCLUDES: a default answer, or a changed core, for input that is no ask
law tree_ffi_malformed:
  for +s: Tr.St
  for +input: String
  for h: {Ft.get_ask(input) == Wr.Bad{} : Wr.Dec<Tr.Ask>}
  {Ft.step(Ft.Live{s}, input) == (Ft.Live{s}, Wr.err("tree: malformed ask")) : Ft.St & String}

# LAW: input left after an ask answers the error form and keeps the core
# EXCLUDES: an answer to an ask followed by garbage
law tree_ffi_trailing:
  for +s: Tr.St
  for +input: String
  for q: Tr.Ask
  for rest: String
  for h: {Ft.get_ask(input) == Wr.Got{q, rest} : Wr.Dec<Tr.Ask>}
  for left: {Wr.end(rest) == False{} : Bool}
  {Ft.step(Ft.Live{s}, input) == (Ft.Live{s}, Wr.err("tree: input left after the ask")) : Ft.St & String}

# LAW: a refused open answers every step with the error form
# EXCLUDES: a core conjured after a refused open
law tree_ffi_refused:
  for input: String
  {Ft.step(Ft.Shut{}, input) == (Ft.Shut{}, Wr.err("tree: the open was refused")) : Ft.St & String}

# LAW: an open with halves that fit the wire opens the empty core that
# splits at those halves, and answers the empty reply
# EXCLUDES: halves read wrong (a lost, added or changed half), a core that
#   starts with a node or a record
law tree_ffi_open:
  for +hs: List<&2, Nat>
  for h: {Bool.and(wire_fits(List.length(&2, Nat, hs)), wire_nats_fit(hs)) == True{} : Bool}
  {Ft.open(Wr.put_list(~Nat, ~Wr.put_nat, hs, "")) == (Ft.Live{Tr.core.start(hs)}, "") : Ft.St & String}

# LAW: an open whose input is no list of halves is refused
# EXCLUDES: a default core for malformed input
law tree_ffi_open_malformed:
  for +input: String
  for h: {Wr.get_list(~Nat, ~Wr.get_nat, input) == Wr.Bad{} : Wr.Dec<List<&2, Nat>>}
  {Ft.open(input) == (Ft.Shut{}, Wr.err("tree: malformed halves")) : Ft.St & String}

# LAW: an open with input left after the halves is refused
# EXCLUDES: a core opened from halves followed by garbage
law tree_ffi_open_trailing:
  for +input: String
  for hs: List<&2, Nat>
  for rest: String
  for h: {Wr.get_list(~Nat, ~Wr.get_nat, input) == Wr.Got{hs, rest} : Wr.Dec<List<&2, Nat>>}
  for left: {Wr.end(rest) == False{} : Bool}
  {Ft.open(input) == (Ft.Shut{}, Wr.err("tree: input left after the halves")) : Ft.St & String}

# LAW: witness: asks and halves that fit exist (the premises above)
# EXCLUDES: a vacuous tree.ask_fits or open premise
law tree_ffi_fits_exists:
  exs q: Tr.Ask
  exs hs: List<&2, Nat>
  {Bool.and(tree.ask_fits(q), Bool.and(wire_fits(List.length(&2, Nat, hs)), wire_nats_fit(hs))) == True{} : Bool}

# LAW: anchors of the encodings Rust writes and reads (crates/eukhe-durable
# src/tree/journal.rs): an ask of each kind, and an answer of each kind
# EXCLUDES: a field order or a tag that differs from the Rust side
law tree_ffi_example:
  {[Ft.put_ask(Tr.Note{Tr.Do{Tr.Put{2n, 1n, 7n}}}, ""), Ft.put_ask(Tr.Note{Tr.Do{Tr.Del{2n}}}, ""), Ft.put_ask(Tr.Note{Tr.Rewind{[Tr.Del{3n}, Tr.Put{2n, 1n, 0n}]}}, ""), Ft.put_ask(Tr.Plan{4n}, ""), Ft.put_ask(Tr.Snap{5n}, ""), Ft.put_ans(Tr.Kept{}, ""), Ft.put_ans(Tr.Took{}, ""), Ft.put_ans(Tr.Cut{[2n, 3n]}, ""), Ft.put_ans(Tr.Effects{[Tr.Start{1n}, Tr.Stop{2n}, Tr.Restore{3n}]}, ""), Ft.put_ans(Tr.Nodes{[Tr.Ent{1n, 0n, 9n}]}, "")] == ["0,0,0,2,1,7,", "0,0,1,2,", "0,1,2,1,3,0,2,1,0,", "1,4,", "2,5,", "0,", "1,", "2,2,2,3,", "3,3,0,1,1,2,2,3,", "4,1,1,0,9,"] : List<&2, String>}

# ---- core entries ----

# LAWS: the entries of the compiled Bend core (bend/core.bend) for the
# thinking ladder, the strict plan and the thinking budgets
# (bend/ffi_effort.bend, bend/ffi_infer.bend, bend/ffi_facts.bend). Each law
# is an open claim about those files; PROOF.bend proves them (as
# Laws.<law>) on the lemmas of PROOF.bend section wire.
#
# R1: a request Rust writes (`put_req`, the grammar of the file's header,
#     every Nat and list length within the wire) reads back whole: no field
#     lost, invented, swapped or reordered, and the rest untouched.
# R2: the entry answers that request with the encoding of the model's
#     decision: the Rust rule is the proven model.
# R3: a malformed request, or one with input left over, answers the
#     entry's error form, never a default decision.
# Every input is free: any facts, maps, levels, tools, caps, budgets and
# any text.

# what fits the wire: a Maybe<Nat> whose Nat fits (None always does)
def core_mfits(m: Maybe<&2, Nat>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{x}:
      wire_fits(x)

# (effort) The thinking ladder: bend/ffi_effort.bend
# --------------------------------------------------

# a list of levels whose length fits (every level's tag does)
def core_lvs_fit(ls: List<&2, Ef.Lv>) -> Bool:
  wire_fits(List.length(&2, Ef.Lv, ls))

def core_facts_fit(f: FEf.Facts) -> Bool:
  match f:
    case FEf.Facts{flag, by_map, explicit, rule, reasoning, plain}:
      Bool.and(core_lvs_fit(reasoning), core_lvs_fit(plain))

def core_effort_fits(q: FEf.Req) -> Bool:
  match q:
    case FEf.Offered{f}:
      core_facts_fit(f)
    case FEf.Clamp{f, l}:
      core_facts_fit(f)
    case FEf.Cycle{f, l, d}:
      core_facts_fit(f)

# the S10 model whose ladder the facts give (bend/infer.bend section 6)
def core_effort_model(f: FEf.Facts) -> Ef.Mdl:
  match f:
    case FEf.Facts{flag, by_map, +explicit, rule, reasoning, plain}:
      If.lad.model(If.lad.reasons(flag, by_map, explicit), explicit, rule, If.Defaults{reasoning, plain})

# LAW R1 a ladder request that fits reads back, and the rest is untouched
# EXCLUDES: a flag, a map entry, a default level, the level or the
#   direction lost, swapped or misread; a request that eats the rest
law core_effort_round_trip:
  for +q: FEf.Req
  for rest: String
  for h: {core_effort_fits(q) == True{} : Bool}
  {FEf.get_req(FEf.put_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FEf.Req>}

# LAW R2 the offer request answers the levels the model offers
# EXCLUDES: a codec that drops or swaps a fact, a default ladder
law core_effort_offered:
  for +f: FEf.Facts
  for h: {core_effort_fits(FEf.Offered{f}) == True{} : Bool}
  {FEf.ffi(FEf.put_req(FEf.Offered{f}, "")) == Wr.put_list(~Ef.Lv, ~FEf.put_lv, Ef.offered(core_effort_model(f)), "") : String}

# LAW R2 the clamp request answers the model's clamp of the level
# EXCLUDES: a clamp of another level or of another model, the level as sent
law core_effort_clamp:
  for +f: FEf.Facts
  for +l: Ef.Lv
  for h: {core_effort_fits(FEf.Clamp{f, l}) == True{} : Bool}
  {FEf.ffi(FEf.put_req(FEf.Clamp{f, l}, "")) == FEf.put_lv(Ef.clamp(core_effort_model(f), l), "") : String}

# LAW R2 the cycle request answers the model's cycle step
# EXCLUDES: a reversed direction, a step of another level or model
law core_effort_cycle:
  for +f: FEf.Facts
  for +l: Ef.Lv
  for +d: Ef.Dir
  for h: {core_effort_fits(FEf.Cycle{f, l, d}) == True{} : Bool}
  {FEf.ffi(FEf.put_req(FEf.Cycle{f, l, d}, "")) == FEf.put_mlv(Ef.cycle(core_effort_model(f), l, d), "") : String}

# LAW R3 a malformed ladder request answers the error form
# EXCLUDES: a default ladder or level for a request it cannot read
law core_effort_malformed:
  for +s: String
  for h: {FEf.get_req(s) == Wr.Bad{} : Wr.Dec<FEf.Req>}
  {FEf.ffi(s) == Wr.err("ladder request: malformed") : String}

# LAW R3 a ladder request with input left over answers the error form
# EXCLUDES: an entry that answers a request followed by garbage
law core_effort_left_over:
  for +q: FEf.Req
  for c: Char
  for rest: String
  for h: {core_effort_fits(q) == True{} : Bool}
  {FEf.ffi(FEf.put_req(q, SCon{c, rest})) == Wr.err("ladder request: input left over") : String}

# LAW R1 anchor and witness: a cycle request is its tag, the facts (flag,
# by_map, explicit map, rule map, reasoning and plain defaults), the
# level and the direction, as `models/ladder.rs` writes them
# EXCLUDES: a vacuous core_effort_round_trip, fields or tags in another
#   order than Rust's
law core_effort_req_example:
  {core_effort_fits(FEf.Cycle{FEf.Facts{True{}, False{}, None{}, Some{Ef.LvMap{Ef.Missing{}, Ef.Null{}, Ef.Wire{}, Ef.Wire{}, Ef.Wire{}, Ef.Null{}, Ef.Missing{}}}, [Ef.Low{}, Ef.High{}], Nil{}}, Ef.Medium{}, Ef.Backward{}}) == True{} : Bool} & {FEf.put_req(FEf.Cycle{FEf.Facts{True{}, False{}, None{}, Some{Ef.LvMap{Ef.Missing{}, Ef.Null{}, Ef.Wire{}, Ef.Wire{}, Ef.Wire{}, Ef.Null{}, Ef.Missing{}}}, [Ef.Low{}, Ef.High{}], Nil{}}, Ef.Medium{}, Ef.Backward{}}, "") == "2,TF0,1,0,1,2,2,2,1,0,2,2,4,0,3,1," : String}

# LAW R2 anchor: a level is its tag off 0 .. max 6; a cycle's answer is 0
# (none) or 1 then the level
# EXCLUDES: level tags the Rust reader reads as other levels
law core_effort_reply_example:
  {FEf.put_lv(Ef.Off{}, FEf.put_lv(Ef.Minimal{}, FEf.put_lv(Ef.Low{}, FEf.put_lv(Ef.Medium{}, FEf.put_lv(Ef.High{}, FEf.put_lv(Ef.Xhigh{}, FEf.put_lv(Ef.Max{}, ""))))))) == "0,1,2,3,4,5,6," : String} & {FEf.put_mlv(None{}, FEf.put_mlv(Some{Ef.High{}}, "")) == "0,1,4," : String}

# LAW R3 witness: a malformed ladder request exists (an unknown tag)
# EXCLUDES: a vacuous core_effort_malformed
law core_effort_malformed_example:
  {FEf.get_req("3,") == Wr.Bad{} : Wr.Dec<FEf.Req>} & {FEf.ffi("3,") == Wr.err("ladder request: malformed") : String}

# (infer) The strict plan: bend/ffi_infer.bend
# --------------------------------------------

def core_tool_fits(t: If.Tool) -> Bool:
  match t:
    case If.Tool{i, p}:
      Bool.and(wire_fits(i), wire_fits(p))

def core_tools_fit(ts: List<&2, If.Tool>) -> Bool:
  match ts:
    case Nil{}:
      True{}
    case Con{t, u}:
      Bool.and(core_tool_fits(t), core_tools_fit(u))

def core_infer_fits(q: FIn.Req) -> Bool:
  match q:
    case FIn.Req{cap, +ts, +need}:
      Bool.and(core_mfits(cap), Bool.and(Bool.and(wire_fits(List.length(&2, If.Tool, ts)), core_tools_fit(ts)), Bool.and(wire_fits(List.length(&2, Nat, need)), wire_nats_fit(need))))

# LAW R1 a strict plan request that fits reads back, and the rest is
# untouched
# EXCLUDES: the cap read as none or the reverse, a tool's id and priority
#   swapped, tools or needed ids lost, added or reordered
law core_infer_round_trip:
  for +q: FIn.Req
  for rest: String
  for h: {core_infer_fits(q) == True{} : Bool}
  {FIn.get_req(FIn.put_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FIn.Req>}

# LAW R2 the entry answers the model's strict plan of the request
# EXCLUDES: a plan of other tools or another cap, a refusal for a request
#   that fits, a plan that ignores the needed tools
law core_infer_answers:
  for +cap: Maybe<&2, Nat>
  for +ts: List<&2, If.Tool>
  for +need: List<&2, Nat>
  for h: {core_infer_fits(FIn.Req{cap, ts, need}) == True{} : Bool}
  {FIn.ffi(FIn.put_req(FIn.Req{cap, ts, need}, "")) == FIn.put_plan(If.plan(cap, ts, need), "") : String}

# LAW R3 a malformed strict plan request answers the error form
# EXCLUDES: a default plan (every tool strict, or none) for a request it
#   cannot read
law core_infer_malformed:
  for +s: String
  for h: {FIn.get_req(s) == Wr.Bad{} : Wr.Dec<FIn.Req>}
  {FIn.ffi(s) == Wr.err("strict plan request: malformed") : String}

# LAW R3 a strict plan request with input left over answers the error form
# EXCLUDES: an entry that answers a request followed by garbage
law core_infer_left_over:
  for +q: FIn.Req
  for c: Char
  for rest: String
  for h: {core_infer_fits(q) == True{} : Bool}
  {FIn.ffi(FIn.put_req(q, SCon{c, rest})) == Wr.err("strict plan request: input left over") : String}

# LAW R1 anchor and witness: a request is the cap (0, or 1 then the cap),
# the tools (count, then id and priority each) and the needed ids
# EXCLUDES: a vacuous core_infer_round_trip, fields in another order than
#   `api/constrained_sampling.rs` writes them
law core_infer_req_example:
  {core_infer_fits(FIn.Req{Some{1n}, [If.Tool{7n, 3n}, If.Tool{9n, 0n}], [9n]}) == True{} : Bool} & {FIn.put_req(FIn.Req{Some{1n}, [If.Tool{7n, 3n}, If.Tool{9n, 0n}], [9n]}, "") == "1,1,2,7,3,9,0,1,9," : String}

# LAW R2 anchor: a plan that fits is 0 then the loose ids; a refusal is 1
# then the tool's id
# EXCLUDES: a refusal the Rust reader reads as a plan, or the reverse
law core_infer_reply_example:
  {FIn.put_plan(If.Fits{[3n, 1n]}, FIn.put_plan(If.Over{7n}, "")) == "0,2,3,1,1,7," : String}

# LAW R3 witness: a malformed strict plan request exists (an unknown cap
# tag)
# EXCLUDES: a vacuous core_infer_malformed
law core_infer_malformed_example:
  {FIn.get_req("2,") == Wr.Bad{} : Wr.Dec<FIn.Req>} & {FIn.ffi("2,") == Wr.err("strict plan request: malformed") : String}

# (facts) The thinking budgets: bend/ffi_facts.bend
# -------------------------------------------------

def core_customs_fit(c: Fx.Customs) -> Bool:
  match c:
    case Fx.Customs{mi, lo, me, hi}:
      Bool.and(core_mfits(mi), Bool.and(core_mfits(lo), Bool.and(core_mfits(me), core_mfits(hi))))

def core_budgets_fit(b: Fx.Budgets) -> Bool:
  match b:
    case Fx.Budgets{mi, lo, me, hi}:
      Bool.and(wire_fits(mi), Bool.and(wire_fits(lo), Bool.and(wire_fits(me), wire_fits(hi))))

def core_mbudgets_fit(m: Maybe<&2, Fx.Budgets>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{b}:
      core_budgets_fit(b)

def core_facts_req_fits(q: FFx.Req) -> Bool:
  match q:
    case FFx.Level{l, c, d}:
      Bool.and(core_customs_fit(c), core_budgets_fit(d))
    case FFx.Room{b, m, a}:
      Bool.and(wire_fits(b), Bool.and(wire_fits(m), wire_fits(a)))
    case FFx.Adjust{base, mm, l, c, d, a}:
      Bool.and(core_mfits(base), Bool.and(wire_fits(mm), Bool.and(core_customs_fit(c), Bool.and(core_budgets_fit(d), wire_fits(a)))))
    case FFx.Google{rule, c, l}:
      Bool.and(core_mbudgets_fit(rule), core_customs_fit(c))
    case FFx.Aux{c, d, a, top}:
      Bool.and(core_customs_fit(c), Bool.and(core_budgets_fit(d), Bool.and(wire_fits(a), wire_fits(top))))

# LAW R1 a budget request that fits reads back, and the rest is untouched
# EXCLUDES: a level, a user's budget, a default budget, a cap or the
#   answer's room lost, swapped or misread; a user's budget read as none
law core_facts_round_trip:
  for +q: FFx.Req
  for rest: String
  for h: {core_facts_req_fits(q) == True{} : Bool}
  {FFx.get_req(FFx.put_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FFx.Req>}

# LAW R2 the level request answers the level's budget
# EXCLUDES: the default budget over the user's, another level's budget
law core_facts_level:
  for +l: Fx.ELv
  for +c: Fx.Customs
  for +d: Fx.Budgets
  for h: {core_facts_req_fits(FFx.Level{l, c, d}) == True{} : Bool}
  {FFx.ffi(FFx.put_req(FFx.Level{l, c, d}, "")) == Wr.put_nat(Fx.budget(c, d, Fx.Lv.of(l)), "") : String}

# LAW R2 the room request answers the budget under the answer's room
# EXCLUDES: the budget, the ceiling and the answer's tokens swapped
law core_facts_room:
  for +b: Nat
  for +m: Nat
  for +a: Nat
  for h: {core_facts_req_fits(FFx.Room{b, m, a}) == True{} : Bool}
  {FFx.ffi(FFx.put_req(FFx.Room{b, m, a}, "")) == Wr.put_nat(Fx.room(b, m, a), "") : String}

# LAW R2 the adjust request answers the fitted ceiling and budget
# EXCLUDES: the caller's cap read as none, the model's cap and the answer's
#   tokens swapped, the ceiling and the budget swapped in the reply
law core_facts_adjust:
  for +base: Maybe<&2, Nat>
  for +mm: Nat
  for +l: Fx.ELv
  for +c: Fx.Customs
  for +d: Fx.Budgets
  for +a: Nat
  for h: {core_facts_req_fits(FFx.Adjust{base, mm, l, c, d, a}) == True{} : Bool}
  {FFx.ffi(FFx.put_req(FFx.Adjust{base, mm, l, c, d, a}, "")) == FFx.put_fit(Fx.adjust(base, mm, l, c, d, a), "") : String}

# LAW R2 the Google request answers the Google budget, the refusal of an
# unordered rule included
# EXCLUDES: a rule read as none, a dynamic budget for an unordered rule
law core_facts_google:
  for +rule: Maybe<&2, Fx.Budgets>
  for +c: Fx.Customs
  for +l: Fx.Lv
  for h: {core_facts_req_fits(FFx.Google{rule, c, l}) == True{} : Bool}
  {FFx.ffi(FFx.put_req(FFx.Google{rule, c, l}, "")) == FFx.put_gb(Fx.gbudget(rule, c, l), "") : String}

# LAW R2 the aux request answers the auxiliary call's output cap
# EXCLUDES: the answer's tokens and the top swapped, a cap past the top
law core_facts_aux:
  for +c: Fx.Customs
  for +d: Fx.Budgets
  for +a: Nat
  for +top: Nat
  for h: {core_facts_req_fits(FFx.Aux{c, d, a, top}) == True{} : Bool}
  {FFx.ffi(FFx.put_req(FFx.Aux{c, d, a, top}, "")) == Wr.put_nat(Fx.aux(c, d, a, top), "") : String}

# LAW R3 a malformed budget request answers the error form
# EXCLUDES: a default budget for a request it cannot read
law core_facts_malformed:
  for +s: String
  for h: {FFx.get_req(s) == Wr.Bad{} : Wr.Dec<FFx.Req>}
  {FFx.ffi(s) == Wr.err("budget request: malformed") : String}

# LAW R3 a budget request with input left over answers the error form
# EXCLUDES: an entry that answers a request followed by garbage
law core_facts_left_over:
  for +q: FFx.Req
  for c: Char
  for rest: String
  for h: {core_facts_req_fits(q) == True{} : Bool}
  {FFx.ffi(FFx.put_req(q, SCon{c, rest})) == Wr.err("budget request: input left over") : String}

# LAW R1 anchor and witness: an adjust request is its tag, the caller's
# cap, the model's cap, the level, the user's budgets, the defaults and
# the answer's tokens, as `api/simple_options.rs` writes them
# EXCLUDES: a vacuous core_facts_round_trip, fields or tags in another
#   order than Rust's
law core_facts_req_example:
  {core_facts_req_fits(FFx.Adjust{Some{100n}, 64n, Fx.EXhigh{}, Fx.Customs{None{}, Some{5n}, None{}, None{}}, Fx.Budgets{1n, 2n, 3n, 4n}, 8n}) == True{} : Bool} & {FFx.put_req(FFx.Adjust{Some{100n}, 64n, Fx.EXhigh{}, Fx.Customs{None{}, Some{5n}, None{}, None{}}, Fx.Budgets{1n, 2n, 3n, 4n}, 8n}, "") == "2,1,100,64,4,0,1,5,0,0,1,2,3,4,8," : String}

# LAW R2 anchor: a Google budget is 0 dynamic, 1 then the tokens, 2
# unordered; a fit is the ceiling, then the budget
# EXCLUDES: replies the Rust reader reads as other values
law core_facts_reply_example:
  {FFx.put_gb(Fx.Dynamic{}, FFx.put_gb(Fx.Tokens{5n}, FFx.put_gb(Fx.Unordered{}, ""))) == "0,1,5,2," : String} & {FFx.put_fit(Fx.Fit{9n, 4n}, "") == "9,4," : String}

# LAW R3 witness: a malformed budget request exists (an unknown tag)
# EXCLUDES: a vacuous core_facts_malformed
law core_facts_malformed_example:
  {FFx.get_req("5,") == Wr.Bad{} : Wr.Dec<FFx.Req>} & {FFx.ffi("5,") == Wr.err("budget request: malformed") : String}

# ---- retry ----

# LAWS (R, retries): when the harness sends a failed request again
# (audit H2, H3, H4, H5, H10, M3, M4). Each law is an open claim about
# the model in bend/retry.bend; PROOF.bend proves them (as Laws.<law>) with
# the lemmas of PROOF.bend sections retry_policy and retry_ffi. The
# classifier, the wait, the failover walk and the stall run as this model,
# compiled (bend/ffi_retry.bend, R7; Rust calls eukhe_bend::rules::retry).
# The deferred job runs as bend/run.bend, compiled (bend/ffi_run.bend).
# The idle deadline stays Rust: the bridge test
# crates/eukhe-durable/src/harness/generation/retry_bridge.rs runs it
# against bend/bridge_retry.bend.

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

# what a retry may cure by a recorded kind (`retryable_kind`): Some{True}
# for a transient kind, Some{False} for a permanent one, None for Unknown
# (the text decides)
def rs.kind(k: R.Cause) -> Maybe<&2, Bool>:
  match k:
    case R.Overloaded{}:
      Some{True{}}
    case R.RateLimit{}:
      Some{True{}}
    case R.ServerError{}:
      Some{True{}}
    case R.StreamDrop{}:
      Some{True{}}
    case R.StreamStalled{}:
      Some{True{}}
    case R.StreamRepeating{}:
      Some{True{}}
    case R.Refusal{}:
      Some{False{}}
    case R.Safety{}:
      Some{False{}}
    case R.PaymentRequired{}:
      Some{False{}}
    case R.Auth{}:
      Some{False{}}
    case R.Permission{}:
      Some{False{}}
    case R.InvalidRequest{}:
      Some{False{}}
    case R.MalformedResponse{}:
      Some{False{}}
    case R.Unknown{}:
      None{}

def rs.by_kind(c: Maybe<&2, Bool>, text: Bool) -> Bool:
  match c:
    case Some{b}:
      b
    case None{}:
      text

# a status a retry may cure (`retryable_status`): 408, 409, 429, or 500
# and above
def rs.status(+s: Nat) -> Bool:
  Bool.or(Nat.is_ge(s, 500n), Bool.or(Nat.is_eq(s, 408n), Bool.or(Nat.is_eq(s, 409n), Nat.is_eq(s, 429n))))

# with no park and no limit: the recorded status; with none, the recorded
# kind; with neither (or Unknown), the text
def rs.recorded(status: Maybe<&2, Nat>, kind: Maybe<&2, R.Cause>, text: Bool) -> Bool:
  match status kind:
    case Some{s} k:
      rs.status(s)
    case None{} Some{k}:
      rs.by_kind(rs.kind(k), text)
    case None{} None{}:
      text

# `FailureFacts::retryable`, as the Rust states it
def rs.retryable(f: R.Facts) -> Bool:
  match f:
    case R.Facts{parked, limit, status, kind, text}:
      Bool.and(Bool.not(Bool.or(parked, limit)), rs.recorded(status, kind, text))

# LAW: the classifier decides exactly as the Rust rule: never after a park
# or a limit; else by the recorded status (408, 409, 429, 500 and above);
# else by the recorded kind (transient yes, permanent no); else (no kind,
# or Unknown) by the text
# EXCLUDES: a listed status (408, 409, 429) not retried, a transient kind
#   not retried, a permanent kind retried, an Unknown kind that does not
#   fall to the text, a text read when a status or a known kind exists
law retry_classifier_exact:
  for f: R.Facts
  {R.retryable(f) == rs.retryable(f) : Bool}

# LAW: anchors of the classifier: a 429 is retried, a 400 with a transient
# text is not, an Unknown kind with a transient text is, a park is not
# EXCLUDES: a spec helper read in a way the Rust does not mean
law retry_classifier_example:
  {[R.retryable(R.Facts{False{}, False{}, Some{429n}, None{}, False{}}), R.retryable(R.Facts{False{}, False{}, Some{200n}, Some{R.Overloaded{}}, True{}}), R.retryable(R.Facts{False{}, False{}, None{}, Some{R.Unknown{}}, True{}}), R.retryable(R.Facts{False{}, False{}, None{}, Some{R.Auth{}}, True{}}), R.retryable(R.Facts{True{}, False{}, Some{503n}, None{}, True{}})] == [True{}, False{}, True{}, False{}, False{}] : List<&2, Bool>}

# (R2) The wait
# -------------
# crates/eukhe-ai/src/utils/retry.rs `retry_wait` (the step, the jitter)
# and `RetryWait::of` (the server's wait and the cap). Rust saturates the
# base, the cap and the server's wait at the wire's largest Nat
# (`eukhe_bend::wire::NAT_MAX`, over 3000 years of ms) and draws the
# jitter uniform in [0, 2^46).

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

# LAW: with no server wait the retry waits its jitter
# EXCLUDES: a wait invented from nothing, a refusal with no server wait
law retry_wait_plain:
  for jitter: Nat
  for cap: Nat
  {R.wait(jitter, None{}, cap) == R.After{jitter} : R.Delay}

# LAW: with no cap (0) the retry waits the longer of its jitter and the
# server's wait, whatever the server asked
# EXCLUDES: a refusal with no cap, a wait longer than both
law retry_wait_uncapped:
  for jitter: Nat
  for s: Nat
  {R.wait(jitter, Some{s}, 0n) == R.After{Nat.max(jitter, s)} : R.Delay}

# LAW: a server wait within the cap: the retry waits the longer of its
# jitter and the server's wait
# EXCLUDES: a refusal of a server wait the cap allows, a wait that adds
#   the two instead of taking the longer
law retry_wait_within_cap:
  for jitter: Nat
  for s: Nat
  for cap: Nat
  for within: {Nat.is_le(s, cap) == True{} : Bool}
  {R.wait(jitter, Some{s}, cap) == R.After{Nat.max(jitter, s)} : R.Delay}

# when the retry goes out: Some{ms}, or None when it is refused
def rs.held(w: R.Delay) -> Maybe<&2, Nat>:
  match w:
    case R.After{ms}:
      Some{ms}
    case R.Refused{server, cap}:
      None{}

# LAW: under a positive cap, a server wait saturated at any c above the
# cap decides the same: the same wait, or a refusal (Rust saturates the
# server's wait at the wire's largest Nat; only the number a refusal
# names can change, for a server wait past that)
# EXCLUDES: a saturation that turns a refusal into a retry or changes a
#   wait
law retry_wait_saturation_exact:
  for jitter: Nat
  for s: Nat
  for cap: Nat
  for c: Nat
  for capped: {Nat.is_gt(cap, 0n) == True{} : Bool}
  for above: {Nat.is_gt(c, cap) == True{} : Bool}
  {rs.held(R.wait(jitter, Some{Nat.min(s, c)}, cap)) == rs.held(R.wait(jitter, Some{s}, cap)) : Maybe<&2, Nat>}

# b doubled k times
def rs.twice(k: Nat, +b: Nat) -> Nat:
  match k:
    case 0n:
      b
    case 1n+j:
      rs.twice(j, Nat.add(b, b))

# LAW: the step of retry `attempt` (1 for the first retry) is the base
# doubled per retry before it, at most the cap, for every base, attempt and
# cap (no product passes the cap: a native Nat never passes 2^48-1)
# EXCLUDES: a step that does not double, doubles once too often, ignores
#   the cap, or overflows past the cap
law retry_step_exact:
  for base: Nat
  for attempt: Nat
  for cap: Nat
  {R.jitter.step(base, attempt, cap) == Nat.min(rs.twice(Nat.sub(attempt, 1n), base), cap) : Nat}

# LAW: anchors of the step: base 100 under cap 600: 100, 200, 400, 600
# EXCLUDES: a step off by one retry
law retry_step_example:
  {[R.jitter.step(100n, 1n, 600n), R.jitter.step(100n, 2n, 600n), R.jitter.step(100n, 3n, 600n), R.jitter.step(100n, 4n, 600n), R.jitter.step(100n, 40n, 600n)] == [100n, 200n, 400n, 600n, 600n] : List<&2, Nat>}

# LAW: the jitter of a draw under a positive step is the draw modulo the
# step (a draw uniform in [0, 2^46) gives a jitter uniform in [0, step) up
# to step/2^46); under a step of 0 it is 0
# EXCLUDES: a jitter at or past the step, a constant jitter (no spread)
law retry_jitter_exact:
  for step: Nat
  for draw: Nat
  for positive: {Nat.is_gt(step, 0n) == True{} : Bool}
  {R.jitter.draw(step, draw) == Nat.mod(draw, step) : Nat}

# LAW: under a step of 0 (a base or a cap of 0) the jitter is 0
# EXCLUDES: a wait drawn from nothing when the policy asks for none
law retry_jitter_zero_step:
  for draw: Nat
  {R.jitter.draw(0n, draw) == 0n : Nat}

# LAW: the wait of a retry (`retry_wait`) is the wait of the jitter drawn
# under its step, with the server's wait and the cap
# EXCLUDES: a retry wait that skips the jitter, the step or the server
law retry_wait_composes:
  for base: Nat
  for attempt: Nat
  for cap: Nat
  for draw: Nat
  for server: Maybe<&2, Nat>
  {R.retry_wait(base, attempt, cap, draw, server) == R.wait(R.jitter.draw(R.jitter.step(base, attempt, cap), draw), server, cap) : R.Delay}

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

# The failover walk as `next_switch` states it (spec helpers)

# a, a+1, ..., a+k-1
def rs.ints(k: Nat, +a: Nat) -> List<&2, Nat>:
  match k:
    case 0n:
      Nil{}
    case 1n+j:
      a <> rs.ints(j, 1n+a)

# the chain in order after the provider `last`, never `last` itself:
# last+1 .. len-1, then 0 .. last-1
def rs.after(+last: Nat, +len: Nat) -> List<&2, Nat>:
  List.append(&2, Nat, rs.ints(Nat.sub(len, 1n+last), 1n+last), rs.ints(Nat.min(last, len), 0n))

# some attempt of ts went to provider x
def rs.tried(+x: Nat, ts: List<&2, R.Tried>) -> Bool:
  match ts:
    case Nil{}:
      False{}
    case t <> rest:
      match t:
        case R.Tried{at, w}:
          Bool.or(Nat.is_eq(at, x), rs.tried(x, rest))

# every provider of xs was tried
def rs.all_tried(xs: List<&2, Nat>, +ts: List<&2, R.Tried>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> rest:
      Bool.and(rs.tried(x, ts), rs.all_tried(rest, ts))

def rs.wait.pick(hit: Bool, w: Maybe<&2, Nat>, +acc: Nat) -> Nat:
  match hit:
    case True{}:
      Maybe.default(&2, Nat, w, 0n)
    case False{}:
      acc

# the server's wait of the newest attempt at x, read oldest first (0 when
# that attempt recorded none); acc: the answer before ts
def rs.wait(+x: Nat, ts: List<&2, R.Tried>, +acc: Nat) -> Nat:
  match ts:
    case Nil{}:
      acc
    case t <> rest:
      match t:
        case R.Tried{at, w}:
          rs.wait(x, rest, rs.wait.pick(Nat.is_eq(at, x), w, acc))

# s when ok, else the pick of the rest
def rs.first(ok: Bool, +s: R.Switch, rest: Maybe<&2, R.Switch>) -> Maybe<&2, R.Switch>:
  match ok:
    case True{}:
      Some{s}
    case False{}:
      rest

# the first provider of xs not tried, at once
def rs.fresh(xs: List<&2, Nat>, +ts: List<&2, R.Tried>) -> Maybe<&2, R.Switch>:
  match xs:
    case Nil{}:
      None{}
    case +x <> rest:
      rs.first(Bool.not(rs.tried(x, ts)), R.Switch{x, 0n}, rs.fresh(rest, ts))

# the first provider of xs whose return wait (the backoff b, never less
# than its server's wait) is positive and at most max
def rs.back(xs: List<&2, Nat>, +ts: List<&2, R.Tried>, +b: Nat, +max: Nat) -> Maybe<&2, R.Switch>:
  match xs:
    case Nil{}:
      None{}
    case +x <> rest:
      +d = Nat.max(b, rs.wait(x, ts, 0n))
      rs.first(Bool.and(Nat.is_gt(d, 0n), Nat.is_le(d, max)), R.Switch{x, d}, rs.back(rest, ts, b, max))

def rs.count(ts: List<&2, R.Tried>) -> Nat:
  match ts:
    case Nil{}:
      0n
    case t <> rest:
      1n+rs.count(rest)

# the provider of the newest attempt: the last of t, ts
def rs.newest(ts: List<&2, R.Tried>, +t: R.Tried) -> Nat:
  match ts:
    case Nil{}:
      match t:
        case R.Tried{at, w}:
          at
    case u <> rest:
      rs.newest(rest, u)

# once every provider was tried: the backoff of the next return is the
# base doubled per earlier return (the attempts past the first len), at
# most max
def rs.returns(all: Bool, +last: Nat, +len: Nat, +ts: List<&2, R.Tried>, +p: R.Policy) -> Maybe<&2, R.Switch>:
  match all:
    case True{}:
      rs.back(rs.after(last, len), ts, Nat.min(rs.twice(Nat.sub(rs.count(ts), len), R.Policy.base(p)), R.Policy.max(p)), R.Policy.max(p))
    case False{}:
      rs.fresh(rs.after(last, len), ts)

# while the switches made (the attempts but the first) are below the
# budget: a fresh provider while one is left, else a return
def rs.budget(ok: Bool, +last: Nat, +len: Nat, +ts: List<&2, R.Tried>, +p: R.Policy) -> Maybe<&2, R.Switch>:
  match ok:
    case True{}:
      rs.returns(rs.all_tried(rs.ints(len, 0n), ts), last, len, ts, p)
    case False{}:
      None{}

# `next_switch`, as the Rust states it: no attempt, no switch
def rs.next(+len: Nat, ts: List<&2, R.Tried>, +p: R.Policy) -> Maybe<&2, R.Switch>:
  match ts:
    case Nil{}:
      None{}
    case +t <> +rest:
      rs.budget(Nat.is_lt(rs.count(rest), R.Policy.switches(p)), rs.newest(rest, t), len, t <> rest, p)

# LAW: the walk decides exactly as `next_switch` states it, for every
# chain, every failed attempt list and every policy
# EXCLUDES: no failover at all (always None), a fresh provider skipped or
#   taken out of chain order, a return before every provider was tried, a
#   backoff that does not double per return or ignores max, a switch past
#   the budget or one short of it, a server wait read from the wrong attempt
law failover_exact:
  for len: Nat
  for ts: List<&2, R.Tried>
  for p: R.Policy
  {R.next(len, ts, p) == rs.next(len, ts, p) : Maybe<&2, R.Switch>}

# LAW: anchors of the walk (base 10, max 300): the next fresh provider in
# chain order; once all were tried, a return after the doubled backoff, or
# the server's longer wait; none past max, past the budget, or with no wait
# EXCLUDES: a spec helper read in a way `next_switch` does not mean
law failover_example:
  {[R.next(3n, [R.Tried{1n, None{}}], R.Policy{8n, 10n, 200n}), R.next(3n, [R.Tried{2n, None{}}], R.Policy{8n, 10n, 200n}), R.next(3n, [R.Tried{0n, None{}}, R.Tried{1n, None{}}, R.Tried{2n, None{}}], R.Policy{8n, 10n, 200n}), R.next(3n, [R.Tried{0n, None{}}, R.Tried{1n, None{}}, R.Tried{2n, None{}}, R.Tried{0n, None{}}], R.Policy{8n, 10n, 200n}), R.next(3n, [R.Tried{0n, Some{50n}}, R.Tried{1n, None{}}, R.Tried{2n, None{}}], R.Policy{8n, 10n, 200n}), R.next(3n, [R.Tried{0n, Some{250n}}, R.Tried{1n, Some{250n}}, R.Tried{2n, None{}}], R.Policy{8n, 10n, 200n})] == [Some{R.Switch{2n, 0n}}, Some{R.Switch{0n, 0n}}, Some{R.Switch{0n, 10n}}, Some{R.Switch{1n, 20n}}, Some{R.Switch{0n, 50n}}, None{}] : List<&2, Maybe<&2, R.Switch>>}

# LAW: anchors of the budget and of a zero backoff: a policy of 1 switch
# allows one switch and no second; a base of 0 never returns without a
# server's wait
# EXCLUDES: a budget off by one, a return that goes out at once
law failover_budget_example:
  {[R.next(2n, [R.Tried{0n, None{}}], R.Policy{1n, 10n, 200n}), R.next(2n, [R.Tried{0n, None{}}, R.Tried{1n, None{}}], R.Policy{1n, 10n, 200n}), R.next(2n, [R.Tried{0n, None{}}, R.Tried{1n, None{}}], R.Policy{8n, 0n, 200n})] == [Some{R.Switch{1n, 0n}}, None{}, None{}] : List<&2, Maybe<&2, R.Switch>>}

def rs.cap_wait(w: Maybe<&2, Nat>, +c: Nat) -> Maybe<&2, Nat>:
  match w:
    case Some{x}:
      Some{Nat.min(x, c)}
    case None{}:
      None{}

# every server wait of ts saturated at c
def rs.cap_waits(ts: List<&2, R.Tried>, +c: Nat) -> List<&2, R.Tried>:
  match ts:
    case Nil{}:
      Nil{}
    case t <> rest:
      match t:
        case R.Tried{at, w}:
          R.Tried{at, rs.cap_wait(w, c)} <> rs.cap_waits(rest, c)

# LAW: server waits saturated at any c above max decide the same walk
# (Rust saturates them at the wire's largest Nat: exact for every max
# below it)
# EXCLUDES: a saturation that returns to a provider whose server asked for
#   more than max, or changes a switch's wait
law failover_wait_saturation_exact:
  for len: Nat
  for ts: List<&2, R.Tried>
  for p: R.Policy
  for c: Nat
  for above: {Nat.is_gt(c, R.Policy.max(p)) == True{} : Bool}
  {R.next(len, rs.cap_waits(ts, c), p) == R.next(len, ts, p) : Maybe<&2, R.Switch>}

# LAW: a base saturated at any c of at least max decides the same walk
# (Rust saturates it at the wire's largest Nat: exact for every max up to
# it)
# EXCLUDES: a saturation that changes a backoff
law failover_base_saturation_exact:
  for len: Nat
  for ts: List<&2, R.Tried>
  for switches: Nat
  for base: Nat
  for max: Nat
  for c: Nat
  for at_least: {Nat.is_le(max, c) == True{} : Bool}
  {R.next(len, ts, R.Policy{switches, Nat.min(base, c), max}) == R.next(len, ts, R.Policy{switches, base, max}) : Maybe<&2, R.Switch>}

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

# LAW: the retry of a stalled stream gets twice the idle deadline it
# stalled under (Rust saturates the deadline at half the wire's largest
# Nat, so twice it stays a wire Nat)
# EXCLUDES: a deadline that grows by less (one ms, a fixed amount) or by
#   more than twice
law stall_retry_doubles:
  for idle: Nat
  {R.stall.next(idle) == Nat.add(idle, idle) : Nat}

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

# (R7) The entry of the compiled core
# -----------------------------------
# bend/ffi_retry.bend `ffi`: the classifier, the wait, the failover walk
# and the stall, called from Rust through crate eukhe-bend in the wire
# format of LAWS.bend section wire. Rust saturates every value (above) so
# each Nat it encodes fits the wire.

# a Maybe<Nat> fits the wire
def rs.mfits(m: Maybe<&2, Nat>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{n}:
      wire_fits(n)

# every attempt of ts fits the wire
def rs.tried_fit(ts: List<&2, R.Tried>) -> Bool:
  match ts:
    case Nil{}:
      True{}
    case t <> rest:
      match t:
        case R.Tried{at, w}:
          Bool.and(Bool.and(wire_fits(at), rs.mfits(w)), rs.tried_fit(rest))

# every Nat of a request fits the wire (and so does the count of a list)
def rs.req_fits(q: Fr.Req) -> Bool:
  match q:
    case Fr.QClassify{f}:
      match f:
        case R.Facts{parked, limit, status, kind, text}:
          rs.mfits(status)
    case Fr.QWait{base, attempt, cap, draw, server}:
      Bool.and(Bool.and(wire_fits(base), wire_fits(attempt)), Bool.and(Bool.and(wire_fits(cap), wire_fits(draw)), rs.mfits(server)))
    case Fr.QFailover{len, +ts, p}:
      match p:
        case R.Policy{switches, base, max}:
          Bool.and(Bool.and(wire_fits(len), Bool.and(wire_fits(R.length(ts)), rs.tried_fit(ts))), Bool.and(wire_fits(switches), Bool.and(wire_fits(base), wire_fits(max))))
    case Fr.QStall{idle}:
      wire_fits(idle)

# LAW: a request that fits the wire reads back, and the rest is untouched
# EXCLUDES: a field read into the wrong slot, a lost or extra attempt, a
#   swapped Bool, a cause read as another cause, a wrong decision tag
law retry_ffi_request_round_trip:
  for q: Fr.Req
  for +rest: String
  for h: {rs.req_fits(q) == True{} : Bool}
  {Fr.get_req(Fr.put_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<Fr.Req>}

# LAW: a decoded request is exactly an encoding: any other input is Bad{}
# EXCLUDES: an unknown tag, cause or Maybe mark read as a value, a request
#   read from a string that no encoder writes (a default for bad input)
law retry_ffi_request_exact:
  for +s: String
  for +q: Fr.Req
  for +rest: String
  for h: {Fr.get_req(s) == Wr.Got{q, rest} : Wr.Dec<Fr.Req>}
  {s == Fr.put_req(q, rest) : String}

# LAW: the entry answers a classify request with the classifier's decision
# EXCLUDES: an entry that answers anything but the model's decision
law retry_ffi_classify:
  for f: R.Facts
  for h: {rs.req_fits(Fr.QClassify{f}) == True{} : Bool}
  {Fr.ffi(Fr.put_req(Fr.QClassify{f}, "")) == Wr.put_bool(R.retryable(f), "") : String}

# LAW: the entry answers a wait request with the model's wait
# EXCLUDES: an entry that answers anything but the model's decision
law retry_ffi_wait:
  for base: Nat
  for attempt: Nat
  for cap: Nat
  for draw: Nat
  for server: Maybe<&2, Nat>
  for h: {rs.req_fits(Fr.QWait{base, attempt, cap, draw, server}) == True{} : Bool}
  {Fr.ffi(Fr.put_req(Fr.QWait{base, attempt, cap, draw, server}, "")) == Fr.put_delay(R.retry_wait(base, attempt, cap, draw, server), "") : String}

# LAW: the entry answers a failover request with the model's next switch
# EXCLUDES: an entry that answers anything but the model's decision
law retry_ffi_failover:
  for len: Nat
  for ts: List<&2, R.Tried>
  for p: R.Policy
  for h: {rs.req_fits(Fr.QFailover{len, ts, p}) == True{} : Bool}
  {Fr.ffi(Fr.put_req(Fr.QFailover{len, ts, p}, "")) == Fr.put_switch(R.next(len, ts, p), "") : String}

# LAW: the entry answers a stall request with the model's next deadline
# EXCLUDES: an entry that answers anything but the model's decision
law retry_ffi_stall:
  for idle: Nat
  for h: {rs.req_fits(Fr.QStall{idle}) == True{} : Bool}
  {Fr.ffi(Fr.put_req(Fr.QStall{idle}, "")) == Wr.put_nat(R.stall.next(idle), "") : String}

# LAW: malformed input answers the error form, never a decision
# EXCLUDES: a default decision for input that is no request
law retry_ffi_malformed:
  for +s: String
  for h: {Fr.get_req(s) == Wr.Bad{} : Wr.Dec<Fr.Req>}
  {Fr.ffi(s) == Wr.err("retry: malformed request") : String}

# LAW: input left after a request answers the error form
# EXCLUDES: a decision for a request followed by garbage
law retry_ffi_trailing:
  for +s: String
  for q: Fr.Req
  for rest: String
  for h: {Fr.get_req(s) == Wr.Got{q, rest} : Wr.Dec<Fr.Req>}
  for left: {Wr.end(rest) == False{} : Bool}
  {Fr.ffi(s) == Wr.err("retry: input left after the request") : String}

# LAW: witness: requests that fit exist (the premise of the laws above)
# EXCLUDES: a vacuous rs.req_fits
law retry_ffi_fits_exists:
  exs q: Fr.Req
  {rs.req_fits(q) == True{} : Bool}

# LAW: anchors of the encodings Rust writes and reads (crates/eukhe-bend
# WIRE.md): a request per decision, and the replies
# EXCLUDES: a field order or a tag that differs from the Rust side
law retry_ffi_example:
  {[Fr.put_req(Fr.QClassify{R.Facts{False{}, True{}, Some{42n}, Some{R.Unknown{}}, True{}}}, ""), Fr.put_req(Fr.QWait{100n, 4n, 200n, 7n, None{}}, ""), Fr.put_req(Fr.QFailover{3n, [R.Tried{0n, None{}}, R.Tried{1n, Some{70n}}], R.Policy{8n, 10n, 200n}}, ""), Fr.put_req(Fr.QStall{30n}, ""), Fr.put_delay(R.After{45n}, ""), Fr.put_delay(R.Refused{90n, 40n}, ""), Fr.put_switch(None{}, ""), Fr.put_switch(Some{R.Switch{1n, 20n}}, "")] == ["0,FT1,42,1,13,T", "1,100,4,200,7,0,", "2,3,2,0,0,1,1,70,8,10,200,", "3,30,", "0,45,", "1,90,40,", "0,", "1,1,20,"] : List<&2, String>}

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

# ---- director_entry ----

# LAWS (S5, the compiled core): the entry bend/ffi_director.bend runs the
# Director stack's step for the Rust code. Each law is an open claim about
# that entry; PROOF.bend proves them (as Laws.<law>) with the lemmas of
# PROOF.bend section director_entry.

# The entry of the compiled core (bend/ffi_director.bend)
# --------------------------------------------------------
# The Rust code sends one loop step as text and reads the loop after it.
# Every number it sends fits the wire: it saturates the counts (the
# budgets, the global budget, the cap) at the wire's largest Nat, 10^14-1
# (`eukhe_bend::wire::NAT_MAX`), a count no loop runs out of.

# the numbers of a layer fit the wire
def dir_layer_fits(l: Dr.Layer) -> Bool:
  match l:
    case Dr.Layer{k, b}:
      Bool.and(wire_fits(k), wire_fits(b))

# every item of xs fits the wire
def dir_layers_fit(xs: List<&2, Dr.Layer>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, t}:
      Bool.and(dir_layer_fits(x), dir_layers_fit(t))

# the numbers of a verdict fit the wire
def dir_verdict_fits(v: Dr.Verdict) -> Bool:
  match v:
    case Dr.Defer{}:
      True{}
    case Dr.Again{}:
      True{}
    case Dr.Yield{}:
      True{}
    case Dr.Stack{l}:
      dir_layer_fits(l)
    case Dr.Leave{}:
      True{}
    case Dr.Abort{}:
      True{}
    case Dr.Lead{}:
      True{}

# every item of xs fits the wire
def dir_verdicts_fit(xs: List<&2, Dr.Verdict>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, t}:
      Bool.and(dir_verdict_fits(x), dir_verdicts_fit(t))

# the numbers of a loop fit the wire
def dir_loop_fits(l: Dr.Loop) -> Bool:
  match l:
    case Dr.Loop{n, +s, e}:
      Bool.and(wire_fits(n), Bool.and(wire_fits(List.length(&2, Dr.Layer, s)), dir_layers_fit(s)))

# the numbers of a request fit the wire
def dir_req_fits(q: FDr.Req) -> Bool:
  match q:
    case FDr.Req{c, l, +vs}:
      Bool.and(wire_fits(c), Bool.and(dir_loop_fits(l), Bool.and(wire_fits(List.length(&2, Dr.Verdict, vs)), dir_verdicts_fit(vs))))

# LAW: a request that fits reads back whole, and the input after it stays
# EXCLUDES: a layer, a verdict, a budget, the cap or the end lost, swapped
#   or misread on the way to the model
law dir_ffi_round_trip:
  for +q: FDr.Req
  for +rest: String
  for h: {dir_req_fits(q) == True{} : Bool}
  {FDr.get_req(FDr.put_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FDr.Req>}

# LAW: the entry answers one step of the model: the loop after the tick
# EXCLUDES: an entry that decides anything but Dr.tick (a default, a
#   second rule), a reply that encodes another loop
law dir_ffi_is_tick:
  for +c: Nat
  for +l: Dr.Loop
  for +vs: List<&2, Dr.Verdict>
  for h: {dir_req_fits(FDr.Req{c, l, vs}) == True{} : Bool}
  {FDr.ffi(FDr.put_req(FDr.Req{c, l, vs}, "")) == FDr.put_loop(Dr.tick(c, l, vs), "") : String}

# LAW: a malformed request answers the error form, never a loop
# EXCLUDES: a default loop for input the decoder refuses
law dir_ffi_malformed:
  for +s: String
  for h: {FDr.get_req(s) == Wr.Bad{} : Wr.Dec<FDr.Req>}
  {FDr.ffi(s) == Wr.err("director: malformed request") : String}

# LAW: a request with input left over answers the error form
# EXCLUDES: a reply to a request followed by anything (a second request
#   glued on, a truncated encoding read as a shorter one)
law dir_ffi_left_over:
  for +s: String
  for +q: FDr.Req
  for +r: String
  for h: {FDr.get_req(s) == Wr.Got{q, r} : Wr.Dec<FDr.Req>}
  for e: {String.is_empty(r) == False{} : Bool}
  {FDr.ffi(s) == Wr.err("director: input left over") : String}

# LAW: witness: a request fits (the premise of the laws above can hold)
law dir_req_fits_example:
  {dir_req_fits(FDr.Req{4n, Dr.Loop{3n, [Dr.Layer{0n, 5n}], Some{Dr.Hand{}}}, [Dr.Stack{Dr.Layer{1n, 1n}}, Dr.Lead{}]}) == True{} : Bool}

# ---- child_env_entry ----

# LAWS (G3, the compiled core): the entry bend/ffi_child_env.bend runs the
# child environment for the Rust code. Each law is an open claim about
# that entry; PROOF.bend proves them (as Laws.<law>) with the lemmas of
# PROOF.bend section child_env_entry.

# The entry of the compiled core (bend/ffi_child_env.bend)
# ---------------------------------------------------------
# The Rust code sends the registry, the keep list, the base and the
# overlay as text, and reads the environment of the child. It sends each
# value as a number (the model never reads a value and never invents a
# variable: env_child_from_merge), and maps the numbers back.

# the length of s fits the wire
def env_str_fits(+s: String) -> Bool:
  wire_fits(String.length(s))

# every item of xs fits the wire
def env_strs_fit(xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, t}:
      Bool.and(env_str_fits(x), env_strs_fit(t))

# the lengths of a variable fit the wire
def env_var_fits(v: Env.Var) -> Bool:
  match v:
    case Env.Var{+n, +x}:
      Bool.and(env_str_fits(n), env_str_fits(x))

# every item of xs fits the wire
def env_vars_fit(xs: List<&2, Env.Var>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, t}:
      Bool.and(env_var_fits(x), env_vars_fit(t))

# the numbers of a request fit the wire
def env_req_fits(q: FEnv.Req) -> Bool:
  match q:
    case FEnv.Req{+r, +k, +b, +o}:
      Bool.and(Bool.and(wire_fits(List.length(&2, String, r)), env_strs_fit(r)), Bool.and(Bool.and(wire_fits(List.length(&2, String, k)), env_strs_fit(k)), Bool.and(Bool.and(wire_fits(List.length(&2, Env.Var, b)), env_vars_fit(b)), Bool.and(wire_fits(List.length(&2, Env.Var, o)), env_vars_fit(o)))))

# LAW: a request that fits reads back whole, and the input after it stays
# EXCLUDES: a name, a value, a registry or keep entry lost, swapped or
#   misread on the way to the model
law env_ffi_round_trip:
  for +q: FEnv.Req
  for +rest: String
  for h: {env_req_fits(q) == True{} : Bool}
  {FEnv.get_req(FEnv.put_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FEnv.Req>}

# LAW: the entry answers the model's environment of the child
# EXCLUDES: an entry that filters anything but Env.child (a second rule, a
#   default environment)
law env_ffi_is_child:
  for +r: List<&2, String>
  for +k: List<&2, String>
  for +b: List<&2, Env.Var>
  for +o: List<&2, Env.Var>
  for h: {env_req_fits(FEnv.Req{r, k, b, o}) == True{} : Bool}
  {FEnv.ffi(FEnv.put_req(FEnv.Req{r, k, b, o}, "")) == Wr.put_list(~Env.Var, ~FEnv.put_var, Env.child(r, k, b, o), "") : String}

# LAW: a malformed request answers the error form, never an environment
# EXCLUDES: a default (empty or unfiltered) environment for bad input
law env_ffi_malformed:
  for +s: String
  for h: {FEnv.get_req(s) == Wr.Bad{} : Wr.Dec<FEnv.Req>}
  {FEnv.ffi(s) == Wr.err("child_env: malformed request") : String}

# LAW: a request with input left over answers the error form
# EXCLUDES: a reply to a request followed by anything
law env_ffi_left_over:
  for +s: String
  for +q: FEnv.Req
  for +r: String
  for h: {FEnv.get_req(s) == Wr.Got{q, r} : Wr.Dec<FEnv.Req>}
  for e: {String.is_empty(r) == False{} : Bool}
  {FEnv.ffi(s) == Wr.err("child_env: input left over") : String}

# LAW: witness: a request fits
law env_req_fits_example:
  {env_req_fits(FEnv.Req{["OPENAI_API_KEY"], ["GITHUB_TOKEN"], [Env.Var{"PATH", "0"}], [Env.Var{"HOME", "1"}]}) == True{} : Bool}

# ---- cvar_entry ----

# LAWS (S4, the compiled core): the entries of bend/ffi_cvar.bend run the
# expansion and the key presses for the Rust code. Each law is an open
# claim about those entries; PROOF.bend proves them (as Laws.<law>) with
# the lemmas of PROOF.bend section cvar_entry.

# The entries of the compiled core (bend/ffi_cvar.bend)
# ------------------------------------------------------
# The Rust code (crates/eukhe-bend/src/rules/cvar.rs) numbers the aliases
# and the keys, and keeps every command that is not a run aside: such a
# command crosses as CToggle{its place} (the model passes it through
# unchanged: alias_runs_body, alias_expands_in_order).

# the numbers of a value fit the wire
def cvar_val_fits(v: Cv.Val) -> Bool:
  match v:
    case Cv.VNat{n}:
      wire_fits(n)
    case Cv.VBool{b}:
      True{}

# the numbers of a command fit the wire
def cvar_cmd_fits(c: Cv.Cmd) -> Bool:
  match c:
    case Cv.CSet{i, v}:
      Bool.and(wire_fits(i), cvar_val_fits(v))
    case Cv.CToggle{i}:
      wire_fits(i)
    case Cv.CRun{n}:
      wire_fits(n)
    case Cv.CGone{n}:
      wire_fits(n)

# every item of xs fits the wire
def cvar_cmds_all(xs: List<&2, Cv.Cmd>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, t}:
      Bool.and(cvar_cmd_fits(x), cvar_cmds_all(t))

# a command list fits the wire
def cvar_cmds_fit(+cs: List<&2, Cv.Cmd>) -> Bool:
  Bool.and(wire_fits(List.length(&2, Cv.Cmd, cs)), cvar_cmds_all(cs))

# an alias fits the wire
def cvar_alias_fits(a: Cv.Alias) -> Bool:
  match a:
    case Cv.Alias{n, b}:
      Bool.and(wire_fits(n), cvar_cmds_fit(b))

# every item of xs fits the wire
def cvar_aliases_all(xs: List<&2, Cv.Alias>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, t}:
      Bool.and(cvar_alias_fits(x), cvar_aliases_all(t))

# a key bind fits the wire
def cvar_bind_fits(k: Cv.KeyBind) -> Bool:
  match k:
    case Cv.KeyBind{n, c}:
      Bool.and(wire_fits(n), cvar_cmds_fit(c))

# every item of xs fits the wire
def cvar_binds_all(xs: List<&2, Cv.KeyBind>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, t}:
      Bool.and(cvar_bind_fits(x), cvar_binds_all(t))

# an alias table fits the wire
def cvar_aliases_fit(+as: List<&2, Cv.Alias>) -> Bool:
  Bool.and(wire_fits(List.length(&2, Cv.Alias, as)), cvar_aliases_all(as))

# a bind table fits the wire
def cvar_binds_fit(+bs: List<&2, Cv.KeyBind>) -> Bool:
  Bool.and(wire_fits(List.length(&2, Cv.KeyBind, bs)), cvar_binds_all(bs))

# LAW: an expand request that fits reads back whole
# EXCLUDES: an alias, a command or a number lost, swapped or misread on
#   the way to the model
law cvar_ffi_round_trip:
  for +as: List<&2, Cv.Alias>
  for +cs: List<&2, Cv.Cmd>
  for +rest: String
  for h: {Bool.and(cvar_aliases_fit(as), cvar_cmds_fit(cs)) == True{} : Bool}
  {FCv.get_xreq(FCv.put_xreq(FCv.Xreq{as, cs}, rest)) == Wr.Got{FCv.Xreq{as, cs}, rest} : Wr.Dec<FCv.Xreq>}

# LAW: the expand entry answers the model's expansion
# EXCLUDES: an entry that expands by any other rule, or answers a default
law cvar_ffi_is_expand:
  for +as: List<&2, Cv.Alias>
  for +cs: List<&2, Cv.Cmd>
  for h: {Bool.and(cvar_aliases_fit(as), cvar_cmds_fit(cs)) == True{} : Bool}
  {FCv.ffi(FCv.put_xreq(FCv.Xreq{as, cs}, "")) == FCv.put_exp(Cv.expand(cs, as), "") : String}

# LAW: a malformed expand request answers the error form
# EXCLUDES: a default expansion (nothing to run) for bad input
law cvar_ffi_malformed:
  for +s: String
  for h: {FCv.get_xreq(s) == Wr.Bad{} : Wr.Dec<FCv.Xreq>}
  {FCv.ffi(s) == Wr.err("cvar: malformed expand request") : String}

# LAW: a bind table that fits opens the press state of that table
# EXCLUDES: a table read with a bind or an alias lost or changed
law cvar_ffi_open:
  for +bs: List<&2, Cv.KeyBind>
  for +as: List<&2, Cv.Alias>
  for h: {Bool.and(cvar_binds_fit(bs), cvar_aliases_fit(as)) == True{} : Bool}
  {FCv.open(FCv.put_table(bs, as, "")) == (FCv.Table{bs, as}, "") : FCv.St & String}

# LAW: a malformed bind table opens the refused state, with the error form
# EXCLUDES: an empty table (every key unbound) for bad input
law cvar_ffi_open_malformed:
  for +s: String
  for h: {FCv.get_table(s) == Wr.Bad{} : Wr.Dec<FCv.St>}
  {FCv.open(s) == (FCv.Refused{}, Wr.err("cvar: malformed press table")) : FCv.St & String}

# LAW: a press of a key answers the model's press, and the table stays
# EXCLUDES: a press by any other rule, a table that changes between
#   presses
law cvar_ffi_press:
  for +bs: List<&2, Cv.KeyBind>
  for +as: List<&2, Cv.Alias>
  for +k: Nat
  for h: {wire_fits(k) == True{} : Bool}
  {FCv.step(FCv.Table{bs, as}, Wr.put_nat(k, "")) == (FCv.Table{bs, as}, FCv.put_exp(Cv.press(bs, k, as), "")) : FCv.St & String}

# LAW: a refused table answers every press with the error form
# EXCLUDES: a press that runs anything after a refused open
law cvar_ffi_refused:
  for +s: String
  {FCv.step(FCv.Refused{}, s) == (FCv.Refused{}, Wr.err("cvar: the press table was refused")) : FCv.St & String}

# LAW: witness: a table and a command list fit
law cvar_fits_example:
  {Bool.and(cvar_binds_fit([Cv.KeyBind{0n, [Cv.CRun{1n}, Cv.CToggle{0n}]}]), Bool.and(cvar_aliases_fit([Cv.Alias{1n, [Cv.CSet{2n, Cv.VBool{True{}}}, Cv.CGone{3n}]}]), cvar_cmds_fit([Cv.CSet{0n, Cv.VNat{7n}}]))) == True{} : Bool}

# ---- run_ffi ----

# LAWS (H4.10): the entry of the run's decisions in the compiled core
# (bend/ffi_run.bend). Each law is an open claim; PROOF.bend section
# run_ffi proves them (as Laws.<law>) from the laws of section wire.
# bend/ffi_run.bend: Rust writes a request (the decision's tag and its
# inputs) with eukhe_bend::wire::Writer, and reads the decision's value
# from the answer. Its codec composes the primitives of bend/wire.bend, so
# these laws rest on LAWS.bend section wire.

# Every Nat of a request fits the wire (at most 14 digits: Rust saturates
# its u64 counts at eukhe_bend::wire::NAT_MAX and its u32s fit)
def run.lim_fits(l: Rn.Lim) -> Bool:
  match l:
    case Rn.Lim{rounds, wait, retries, notes}:
      Bool.and(wire_fits(rounds), Bool.and(wire_fits(wait), Bool.and(wire_fits(retries), wire_fits(notes))))

def run.at_fits(t: Rn.At) -> Bool:
  match t:
    case Rn.At{attempt, notes, waited, compacted}:
      Bool.and(wire_fits(attempt), Bool.and(wire_fits(notes), wire_fits(waited)))

def run.rcfg_fits(c: Rn.RCfg) -> Bool:
  match c:
    case Rn.RCfg{long, leak, redirect, repeat}:
      Bool.and(wire_fits(long), Bool.and(wire_fits(leak), Bool.and(wire_fits(redirect), wire_fits(repeat))))

def run.stuck_fits(s: Rn.Stuck) -> Bool:
  match s:
    case Rn.Truncated{}:
      True{}
    case Rn.Leaked{}:
      True{}
    case Rn.Repeats{before}:
      wire_fits(before)

def run.ask_fits(a: FRn.Ask) -> Bool:
  match a:
    case FRn.AskReply{l, t, reply}:
      Bool.and(run.lim_fits(l), run.at_fits(t))
    case FRn.AskEnded{m}:
      True{}
    case FRn.AskPrepare{compacted, th}:
      True{}
    case FRn.AskCompact{over, got}:
      True{}
    case FRn.AskRound{l, count, stops, reset}:
      Bool.and(run.lim_fits(l), wire_fits(count))
    case FRn.AskRecover{rc, s, k, row}:
      Bool.and(run.rcfg_fits(rc), Bool.and(run.stuck_fits(s), wire_fits(row)))
    case FRn.AskPoll{retryable, failures, retries}:
      Bool.and(wire_fits(failures), wire_fits(retries))

# Every Nat of an answer fits the wire
def run.end_fits(e: Rn.End) -> Bool:
  match e:
    case Rn.EndStop{}:
      True{}
    case Rn.EndReset{}:
      True{}
    case Rn.EndCapped{}:
      True{}
    case Rn.EndNext{count}:
      wire_fits(count)

def run.help_fits(h: Rn.Help) -> Bool:
  match h:
    case Rn.Runs{}:
      True{}
    case Rn.Redoes{row}:
      wire_fits(row)
    case Rn.Stands{}:
      True{}
    case Rn.Quits{}:
      True{}

# LAW: every request whose Nats fit the wire reads back as itself, and its
# reading consumes exactly its encoding
# EXCLUDES: a field read into another, a wrong tag, a lost or eaten rest
law run_ffi_ask_round_trip:
  for +a: FRn.Ask
  for +rest: String
  for +h: {run.ask_fits(a) == True{} : Bool}
  {FRn.get_ask(FRn.put_ask(a, rest)) == Wr.Got{a, rest} : Wr.Dec<FRn.Ask>}

# LAW: witness: a request whose Nats fit the wire exists
law run_ffi_ask_fits_witness:
  exs a: FRn.Ask
  {run.ask_fits(a) == True{} : Bool}

# LAW: the entry answers a request with the value of its decision
# EXCLUDES: an entry that answers another decision, or a default
law run_ffi_answers:
  for +a: FRn.Ask
  for +h: {run.ask_fits(a) == True{} : Bool}
  {FRn.ffi(FRn.put_ask(a, "")) == FRn.answer(a) : String}

# LAW: a request with input left over after it is refused
# EXCLUDES: trailing input read as part of a request, or ignored
law run_ffi_refuses_left_over:
  for +a: FRn.Ask
  for +rest: String
  for +h: {run.ask_fits(a) == True{} : Bool}
  for +more: {String.is_empty(rest) == False{} : Bool}
  {FRn.ffi(FRn.put_ask(a, rest)) == Wr.err("run: input left over after the request") : String}

# LAW: witness: input is left over after a request
law run_ffi_left_over_witness:
  exs rest: String
  {String.is_empty(rest) == False{} : Bool}

# LAW: a malformed request answers the error form, never a decision
# EXCLUDES: a default decision for input the entry cannot read
law run_ffi_refuses_malformed:
  for +s: String
  for +bad: {FRn.get_ask(s) == Wr.Bad{} : Wr.Dec<FRn.Ask>}
  {FRn.ffi(s) == Wr.err("run: malformed request") : String}

# LAW: witness: a malformed request exists
law run_ffi_malformed_witness:
  exs s: String
  {FRn.get_ask(s) == Wr.Bad{} : Wr.Dec<FRn.Ask>}

# LAW: every answer reads back as itself: the step after a reply, what
# preparation does, how a round ends, what a recovery does, the reply a
# message makes (Rust's Reader reads the same grammar)
# EXCLUDES: two answers with one encoding, an answer Rust misreads
law run_ffi_then_round_trip:
  for +x: Rn.Then
  for +rest: String
  {FRn.get_then(FRn.put_then(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Rn.Then>}

law run_ffi_prepared_round_trip:
  for +x: Rn.Prepared
  for +rest: String
  {FRn.get_prepared(FRn.put_prepared(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Rn.Prepared>}

law run_ffi_end_round_trip:
  for +x: Rn.End
  for +rest: String
  for +h: {run.end_fits(x) == True{} : Bool}
  {FRn.get_end(FRn.put_end(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Rn.End>}

law run_ffi_help_round_trip:
  for +x: Rn.Help
  for +rest: String
  for +h: {run.help_fits(x) == True{} : Bool}
  {FRn.get_help(FRn.put_help(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Rn.Help>}

law run_ffi_reply_round_trip:
  for +x: Rn.Reply
  for +rest: String
  {FRn.get_reply(FRn.put_reply(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Rn.Reply>}

# LAW: witness: answers whose Nats fit the wire exist
law run_ffi_answer_fits_witness:
  exs e: Rn.End
  exs x: Rn.Help
  {Bool.and(run.end_fits(e), run.help_fits(x)) == True{} : Bool}
