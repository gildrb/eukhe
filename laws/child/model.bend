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
  {Ch.look(cfg, w, e, Ch.PollFailed{}) == ChildMisses(w, e) : Ch.Next}

# LAW child_settled_child_ends_the_watch (K1, laws/child/exact.bend): a
# poll that reads the child settled ends the watch, whatever the settings,
# the clock and the elapsed ms: a child that replied to its parent ends it
# with no report, one that settled without a reply owes Completed, one
# that failed or is gone owes Failed
# EXCLUDES: a settled child watched on, a reply reported again, a failed
#   or gone child reported as completed (or the reverse), a verdict on a
#   settled child that depends on the clock
law child_settled_child_ends_the_watch:
  for +cfg: Ch.Cfg
  for +w: Ch.W
  for +e: Nat
  {Ch.look(cfg, w, e, Ch.Answered{True{}}) == Ch.Quiet{} : Ch.Next} &                # K1: settled with a reply: no report
  {Ch.look(cfg, w, e, Ch.Answered{False{}}) == Ch.Owe{Ch.Completed{}} : Ch.Next} &   # K1: settled without one: Completed
  {Ch.look(cfg, w, e, Ch.Broke{}) == Ch.Owe{Ch.Failed{}} : Ch.Next} &                # K1: failed: Failed
  {Ch.look(cfg, w, e, Ch.Gone{}) == Ch.Owe{Ch.Failed{}} : Ch.Next}                   # K1: gone: Failed

# LAW child_token_is_progress (K1): progress is a token: a first token
# (the watch held none) is progress, the watch goes on with a full clock
# on it; a poll of an unsettled child that reads no token is no progress,
# whatever the watch holds: it spends the e ms elapsed as a quiet poll
# does (ChildSpends) and sets the failed polls in a row back to full
# EXCLUDES: a first token read as no progress (a child that just started
#   stalled), a poll with no token read as progress (a hung child watched
#   forever) or one that keeps the clock
law child_token_is_progress:
  for +cfg: Ch.Cfg
  for +tok: Maybe<&2, Nat>
  for +l: Nat
  for +n: Nat
  for +e: Nat
  for +x: Nat
  {Ch.look(cfg, Ch.W{None{}, l, n}, e, Ch.Busy{Some{x}}) == Ch.Watch{Ch.W.fresh(cfg, Some{x})} : Ch.Next} &
  {Ch.look(cfg, Ch.W{tok, l, n}, e, Ch.Busy{None{}}) == ChildSpends(tok, l, e, Ch.Cfg.fails(cfg)) : Ch.Next}

# LAW child_other_token_is_progress (K1): a token other than the one the
# watch holds (y is not x) is progress: the watch goes on with a full
# clock on the new token. Unlike child_progress_is_not_a_stall, the
# premise is the tokens' inequality itself, not the code's test
# EXCLUDES: a changed token read as no progress (a working child stalled),
#   a clock that keeps the old token or is not refilled
law child_other_token_is_progress:
  for +cfg: Ch.Cfg
  for +y: Nat
  for +l: Nat
  for +n: Nat
  for +e: Nat
  for +x: Nat
  for other: {Nat.is_eq(y, x) == False{} : Bool}
  {Ch.look(cfg, Ch.W{Some{y}, l, n}, e, Ch.Busy{Some{x}}) == Ch.Watch{Ch.W.fresh(cfg, Some{x})} : Ch.Next}

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
# phase's move, the abort. The three rules below (ChildActed, ChildMove,
# ChildAbort) are the rules the entry law child_ffi_answers
# (laws/child/exact.bend) answers every request from.

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

# LAW child_silent_never_reports: a silent task never reports to its parent
law child_silent_never_reports:
  for +cfg: Ch.Cfg
  for +w: Ch.W
  for +e: Nat
  for o: Ch.Obs
  {Ch.Call.reports(Ch.verdict(cfg, w, e, o, Ch.Silent{})) == False{} : Bool}

# LAW child_report_move_is_owe: the move, carried out, is the model's report rule `owe`, so the
# report laws above hold for the task the Rust code runs
law child_report_move_is_owe:
  for f: Maybe<&2, Ch.Fate>
  for k: Ch.Report
  for +n: Nat
  for open: Bool
  for inbox: List<&2, Ch.Sub>
  {Ch.owe.do(Ch.owe.next(f, n), k, n, open, inbox) == Ch.owe(f, k, n, open, inbox) : Ch.St}

