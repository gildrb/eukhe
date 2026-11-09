# eukhe: the laws of area child: the task (H5: every subagent reports back
# exactly once) and its decisions

import Base
import ../../bend/child.bend as Ch

# (H5) Every subagent reports back exactly once
# ---------------------------------------------
# bend/child.bend: the parent's task on one child. The watch's clock
# counts down the ms of no progress left (`left`, full: subagentStallMs)
# and the failed polls in a row left (`tries`, full: CHILD_POLL_FAILURES).

# LAW child_stalls_in_time: quiet polls (the child unsettled with the token the watch holds,
# or a failed poll), at least as many as the ms left on the clock, end the
# watch: each poll takes 1 ms or more
law child_stalls_in_time:
  for +cfg: Ch.Cfg
  for +w: Ch.W
  for +h: Ch.Hush
  for +hs: List<&2, Ch.Hush>
  for long: {Nat.is_le(Ch.W.left(w), List.length(&2, Ch.Hush, h <> hs)) == True{} : Bool}
  {Ch.Next.watching(Ch.hush(h <> hs, cfg, Ch.Watch{w})) == False{} : Bool}

# LAW child_unreachable_in_time: failed polls in a row, as many as the tries left, end the watch
law child_unreachable_in_time:
  for +cfg: Ch.Cfg
  for +w: Ch.W
  for +d: Nat
  for +ds: List<&2, Nat>
  for long: {Nat.is_le(Ch.W.tries(w), List.length(&2, Nat, d <> ds)) == True{} : Bool}
  {Ch.Next.watching(Ch.hush(Ch.misses(d <> ds), cfg, Ch.Watch{w})) == False{} : Bool}

# LAW child_clock_bounded: whatever a poll reads, the clock stays at most full: the bounds
# above are at most subagentStallMs and CHILD_POLL_FAILURES polls
law child_clock_bounded:
  for +cfg: Ch.Cfg
  for +w: Ch.W
  for +e: Nat
  for +o: Ch.Obs
  for full: {Ch.within(cfg, Ch.Watch{w}) == True{} : Bool}
  {Ch.within(cfg, Ch.look(cfg, w, e, o)) == True{} : Bool}

# LAW child_progress_is_not_a_stall: a poll that reads a new token (progress) is never a stall: the
# watch goes on with a full clock
law child_progress_is_not_a_stall:
  for +cfg: Ch.Cfg
  for +w: Ch.W
  for +e: Nat
  for +x: Nat
  for news: {Ch.moved(Ch.W.tok(w), Some{x}) == True{} : Bool}
  {Ch.look(cfg, w, e, Ch.Busy{Some{x}}) == Ch.Watch{Ch.W.fresh(cfg, Some{x})} : Ch.Next}

# the clock after a poll with no progress that took e ms, the watch
# holding token tok with l ms left, `over` when e reached l: a stall; else
# the watch goes on holding tok with e ms fewer left and n failed polls left
def ChildSpent(over: Bool, tok: Maybe<&2, Nat>, +l: Nat, +e: Nat, +n: Nat) -> Ch.Next:
  match over:
    case True{}:
      Ch.Owe{Ch.Stalled{}}
    case False{}:
      Ch.Watch{Ch.W{tok, Nat.sub(l, e), n}}

def ChildSpends(tok: Maybe<&2, Nat>, +l: Nat, +e: Nat, +n: Nat) -> Ch.Next:
  ChildSpent(Nat.is_le(l, e), tok, l, e, n)

# LAW child_quiet_poll_spends_time: a poll that reads the child unsettled
# with the token the watch holds (no news) and took e ms since the last
# spends those e ms: when the ms left are at most e the watch ends owing a
# stalled report; else it goes on holding the same token, e ms fewer left,
# and its failed polls in a row back to full (this poll answered). This is
# the decision the task runs (`look`, which `verdict` and the entry
# carry), so a child hung while reporting busy is stalled in time
# EXCLUDES: a busy poll with no news that keeps the clock (spends 0 ms),
#   spends a wrong amount, refills the ms left, changes the token, or
#   keeps the failed polls in a row
law child_quiet_poll_spends_time:
  for +cfg: Ch.Cfg
  for +w: Ch.W
  for +e: Nat
  {Ch.look(cfg, w, e, Ch.Busy{Ch.W.tok(w)}) == ChildSpends(Ch.W.tok(w), Ch.W.left(w), e, Ch.Cfg.fails(cfg)) : Ch.Next}

# the verdict on a failed poll that took e ms, the watch holding token
# tok, l ms and n tries left, `last` when at most one try is left:
# unreachable; else the e ms are spent as on a quiet poll, one try fewer
# left
def ChildMissed(last: Bool, tok: Maybe<&2, Nat>, +l: Nat, +e: Nat, +n: Nat) -> Ch.Next:
  match last:
    case True{}:
      Ch.Owe{Ch.Unreachable{}}
    case False{}:
      ChildSpends(tok, l, e, Nat.sub(n, 1n))

def ChildMisses(w: Ch.W, +e: Nat) -> Ch.Next:
  match w:
    case Ch.W{tok, +l, +n}:
      ChildMissed(Nat.is_le(n, 1n), tok, l, e, n)

# LAW child_failed_poll_spends_try_and_time: a failed poll (the probe got
# no answer) that took e ms since the last spends one try and the e ms: on
# the last try left (or none) the watch ends owing an unreachable report;
# else when the ms left are at most e it ends owing a stalled report; else
# it goes on holding the same token, e ms fewer and one try fewer left.
# This is the decision the task runs (`look`), so a child that stops
# answering is unreachable in time
# EXCLUDES: a failed poll that keeps or refills the tries, spends no or a
#   wrong amount of ms, reports stalled on the last try, or changes the
#   token
law child_failed_poll_spends_try_and_time:
  for +cfg: Ch.Cfg
  for +w: Ch.W
  for +e: Nat
  {Ch.look(cfg, w, e, Ch.Lost{}) == ChildMisses(w, e) : Ch.Next}

# The report laws hold after any events: task steps (polls), the parent's
# deliveries and withdrawals of any submission id, its aborts, closes and
# reopens, and task aborts and deletes, in any order. The parent's inbox
# keeps every submission of the report, each queued, withdrawn or placed.

# LAW child_one_live: at most one submission of the report is live (queued or placed):
# the task submits again only once its last submission is withdrawn, so
# no two ids of the report can both reach the transcript
law child_one_live:
  for +cfg: Ch.Cfg
  for +evs: List<&2, Ch.Ev>
  {Nat.is_le(Ch.live(Ch.St.inbox(Ch.run(evs, cfg, Ch.St.init(cfg)))), 1n) == True{} : Bool}

# LAW child_report_once: at most one submission of the report is placed: the parent's
# transcript holds the report at most once
law child_report_once:
  for +cfg: Ch.Cfg
  for +evs: List<&2, Ch.Ev>
  {Nat.is_le(Ch.St.placed(Ch.run(evs, cfg, Ch.St.init(cfg))), 1n) == True{} : Bool}

# LAW child_resubmits_per_abort: the report is submitted at most once more than the parent withdrew
# (an abort, a close, a withdrawal of one input): a resubmission follows a
# withdrawal
law child_resubmits_per_abort:
  for +cfg: Ch.Cfg
  for +evs: List<&2, Ch.Ev>
  {Nat.is_le(List.length(&2, Ch.Sub, Ch.St.inbox(Ch.run(evs, cfg, Ch.St.init(cfg)))), Nat.add(Ch.cuts(evs), 1n)) == True{} : Bool}

# LAW child_delivered_once: a report the task owes reaches the parent exactly once when the
# parent reopens, the task takes three steps (the first may run a pending
# abort) and the parent's run places the submission the task then waits
# on (its owed id m): placed in its transcript, or read by the parent
# itself before (rlm.collect): the report is never lost
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
  {Ch.St.reached(Ch.run([Ch.Reopen{}, Ch.Poll{d1, o1}, Ch.Poll{d2, o2}, Ch.Poll{d3, o3}, Ch.Deliver{m}], cfg, Ch.run(evs, cfg, Ch.St.init(cfg)))) == 1n : Nat}

# LAW child_read_never_wakes: once the parent read the report itself (rlm.collect), no
# submission of it waits in the parent's inbox or reaches its transcript,
# whatever happens next: a parent that already answered is never woken
# for a turn that restates what it read
# EXCLUDES: a read that leaves the queued notice in the inbox, a task that
#   submits the report again after the read
law child_read_never_wakes:
  for +cfg: Ch.Cfg
  for +evs: List<&2, Ch.Ev>
  for +later: List<&2, Ch.Ev>
  for read: {Ch.St.read(Ch.run(evs, cfg, Ch.St.init(cfg))) == 1n : Nat}
  {Nat.add(Ch.St.queued(Ch.run(later, cfg, Ch.run(evs, cfg, Ch.St.init(cfg)))), Ch.St.placed(Ch.run(later, cfg, Ch.run(evs, cfg, Ch.St.init(cfg))))) == 0n : Nat}

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
# it under n; queued, wait; withdrawn, owe it under n + 1; placed or read
# by the parent, end
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
        case Ch.Read{}:
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

# LAW child_task_call: the task's call on a poll is the watch's verdict (`look`, which
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

# LAW child_silent_never_reports: a silent task never reports to its parent
law child_silent_never_reports:
  for +cfg: Ch.Cfg
  for +w: Ch.W
  for +e: Nat
  for o: Ch.Obs
  {Ch.Call.reports(Ch.verdict(cfg, w, e, o, Ch.Silent{})) == False{} : Bool}

# LAW child_report_move: the report phase's move is the one report rule
# EXCLUDES: a second submission while one is queued, a resubmission under
# the same id, an end before the report is placed or read
law child_report_move:
  for f: Maybe<&2, Ch.Fate>
  for +n: Nat
  {Ch.owe.next(f, n) == ChildMove(f, n) : Ch.Move}

# LAW child_report_move_is_owe: the move, carried out, is the model's report rule `owe`, so the
# report laws above hold for the task the Rust code runs
law child_report_move_is_owe:
  for f: Maybe<&2, Ch.Fate>
  for k: Ch.Report
  for +n: Nat
  for open: Bool
  for inbox: List<&2, Ch.Sub>
  {Ch.owe.do(Ch.owe.next(f, n), k, n, open, inbox) == Ch.owe(f, k, n, open, inbox) : Ch.St}

# LAW child_abort_rule: the abort's rule
# EXCLUDES: a delete with no report, a cancel that reports, an abort that
# loses or restarts an owed report
law child_abort_rule:
  for ph: Ch.Ph
  for del: Bool
  {Ch.cut.ph(ph, del) == ChildAbort(ph, del) : Ch.Ph}
