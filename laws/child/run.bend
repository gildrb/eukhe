# eukhe: the laws of area child: the task's step and run
#
# Ch.step moves the task and the parent's inbox on one event and Ch.run
# folds the events of a history; the H5 report laws of laws/child/model.bend
# (child_one_live, child_report_once, child_resubmits_per_abort,
# child_delivered_once, child_read_never_wakes) read Ch.run. The laws here
# state what bend/child.bend's header requires of one step and of the run,
# for every setting, state and history (H5):
#
# S1: the run of a history is the step on each event, oldest first.
# S2: the task's own step (a poll) does what the decisions the Rust task
#     runs say: a watched child gets the call (`verdict`, inbox mode), an
#     owed report the move (`owe.next`) on the fate of its newest
#     submission under the owed id, a marked task the abort (`cut.ph`),
#     an ended task nothing. It submits one queued submission, and only
#     when the report has none under the owed id and the parent is open (a
#     closing parent admits no submission); an abort submits nothing.
# S3: a cancel or a delete only marks the task; the abort runs at its next
#     step, once, and a delete stays a delete.
# S4: the parent's events never move the task. Its run places and its
#     withdrawal withdraws the queued submission it names, its abort and
#     its close withdraw every queued one; each submission settles once (a
#     withdrawal that loses the race to a placement leaves it placed); a
#     close and a reopen, and nothing else, set its openness.
# S5: the parent's read reaches only an owed report: the newest submission
#     under the owed id, queued or withdrawn, is read, one placed stays
#     placed; with no such submission a read one stands for it.

import Base
import ../../bend/child.bend as Ch

# What the laws observe
# ---------------------

# the parent of the state s is open
def chr_open(s: Ch.St) -> Bool:
  match s:
    case Ch.St{ph, cut, open, inbox}:
      open

# the abort mark of the state s
def chr_cut(s: Ch.St) -> Maybe<&2, Bool>:
  match s:
    case Ch.St{ph, cut, open, inbox}:
      cut

# the mark asks for a delete (no mark: no)
def chr_deletes(cut: Maybe<&2, Bool>) -> Bool:
  match cut:
    case None{}:
      False{}
    case Some{d}:
      d

# the parent's inbox after event e on the state of phase ph, mark cut,
# openness open and inbox xs
def chr_on(+cfg: Ch.Cfg, ph: Ch.Ph, cut: Maybe<&2, Bool>, open: Bool, xs: List<&2, Ch.Sub>, e: Ch.Ev) -> List<&2, Ch.Sub>:
  Ch.St.inbox(Ch.step(cfg, Ch.St{ph, cut, open, xs}, e))

# some submission of the inbox has id n
def chr_has(inbox: List<&2, Ch.Sub>, +n: Nat) -> Bool:
  match inbox:
    case Nil{}:
      False{}
    case s <> rest:
      match s:
        case Ch.Sub{i, f}:
          Bool.or(Nat.is_eq(i, n), chr_has(rest, n))

# the newest submission of the inbox (the first) has id n
def chr_newest_is(inbox: List<&2, Ch.Sub>, n: Nat) -> Bool:
  match inbox:
    case Nil{}:
      False{}
    case s <> rest:
      match s:
        case Ch.Sub{i, f}:
          Nat.is_eq(i, n)

# a submission with fate f has settled (withdrawn, placed or read)
def chr_settled(f: Ch.Fate) -> Bool:
  match f:
    case Ch.Queued{}:
      False{}
    case Ch.Withdrawn{}:
      True{}
    case Ch.Placed{}:
      True{}
    case Ch.Read{}:
      True{}

# e is an event of the parent: a placement, a withdrawal, an abort, a
# close, a reopen or a read (not the task's step, not its cancel or delete)
def chr_parents(e: Ch.Ev) -> Bool:
  match e:
    case Ch.Poll{dt, o}:
      False{}
    case Ch.Deliver{m}:
      True{}
    case Ch.Withdraw{m}:
      True{}
    case Ch.Abort{}:
      True{}
    case Ch.Shut{}:
      True{}
    case Ch.Reopen{}:
      True{}
    case Ch.Cut{del}:
      False{}
    case Ch.Collect{}:
      True{}

# What the task does with a decision
# ----------------------------------

# the phase a watching task takes on a call: watch on with the call's
# clock; owe the report the call makes, under the first id (1); end when
# the call settles the child with no report
def chr_called(c: Ch.Call) -> Ch.Ph:
  match c:
    case Ch.Watches{w}:
      Ch.Watching{w}
    case Ch.Reports{k}:
      Ch.Owing{k, 1n}
    case Ch.Settles{why}:
      Ch.Ended{}

# the phase a task that owes report k under id n takes on a move: it owes
# k under the id the move submits or resubmits it under, under n while it
# waits, and ends once the report is delivered
def chr_moved(mv: Ch.Move, k: Ch.Report, n: Nat) -> Ch.Ph:
  match mv:
    case Ch.Submit{m}:
      Ch.Owing{k, m}
    case Ch.Await{}:
      Ch.Owing{k, n}
    case Ch.Resubmit{m}:
      Ch.Owing{k, m}
    case Ch.Delivered{}:
      Ch.Ended{}

# the inbox after the task's step: one new queued submission n in front
# when it sent one
def chr_sent(sent: Bool, n: Nat, inbox: List<&2, Ch.Sub>) -> List<&2, Ch.Sub>:
  match sent:
    case True{}:
      Ch.Sub{n, Ch.Queued{}} <> inbox
    case False{}:
      inbox

# The run
# -------

# LAW child_run_folds (H5, S1): the run of no event is the state it starts
# from, and the run of a history and one more event is the step on that
# event from the run of the history: a run takes every event once, oldest
# first
# EXCLUDES: a run that drops, repeats, reorders or invents events (the run
#   that keeps its state, `run(evs, cfg, s) = s`, passes every report law
#   of laws/child/model.bend: the initial state owes nothing and holds no
#   submission), a run that ignores the state it starts from
law child_run_folds:
  for +cfg: Ch.Cfg
  for +s: Ch.St
  for +evs: List<&2, Ch.Ev>
  for +e: Ch.Ev
  {Ch.run(Nil{}, cfg, s) == s : Ch.St} &
  {Ch.run(List.append(&2, Ch.Ev, evs, [e]), cfg, s) == Ch.step(cfg, Ch.run(evs, cfg, s), e) : Ch.St}

# The task's step
# ---------------

# LAW child_watch_takes_the_call (H5, S2): the step of a watching task
# with no abort mark, on a poll that read o, 1 + dt ms after the last, does
# what the call the Rust task runs says (`verdict`, inbox mode): it watches
# on with the call's clock, owes the call's report under the first id (1),
# or ends when the call settles the child with no report; it clears no
# mark, submits nothing and leaves the parent as open as it was
# EXCLUDES: a watch that never owes its report (a task that never owes
#   passes every report law) or owes another, a first id other than 1, a
#   child that replied reported again, a poll that counts no ms, a
#   submission from a watching task
law child_watch_takes_the_call:
  for +cfg: Ch.Cfg
  for +w: Ch.W
  for +open: Bool
  for +inbox: List<&2, Ch.Sub>
  for +dt: Nat
  for +o: Ch.Obs
  {Ch.step(cfg, Ch.St{Ch.Watching{w}, None{}, open, inbox}, Ch.Poll{dt, o}) == Ch.St{chr_called(Ch.verdict(cfg, w, 1n+dt, o, Ch.Inbox{})), None{}, open, inbox} : Ch.St}

# LAW child_first_report_goes_out (H5, S2): a new task whose first poll's
# call reports (the child failed, is gone, settled without a reply, stalled
# or is unreachable: `verdict` on the full clock, inbox mode) submits the
# report at its next step under the first id (1), and once the parent's run
# places that submission the report reached the parent exactly once. No
# reopen is needed: a new task's parent is open, nothing is marked, nothing
# was submitted before
# EXCLUDES: a new task that starts closed, marked or not watching, a watch
#   that never owes, a first submission under another id or not queued
law child_first_report_goes_out:
  for +cfg: Ch.Cfg
  for +d1: Nat
  for +o1: Ch.Obs
  for +d2: Nat
  for +o2: Ch.Obs
  for reports: {Ch.Call.reports(Ch.verdict(cfg, Ch.W.fresh(cfg, None{}), 1n+d1, o1, Ch.Inbox{})) == True{} : Bool}
  {Ch.St.reached(Ch.run([Ch.Poll{d1, o1}, Ch.Poll{d2, o2}, Ch.Deliver{1n}], cfg, Ch.St.init(cfg))) == 1n : Nat}

# LAW child_owing_submits_once (H5, S2): the step of a task that owes
# report k under id n, with no abort mark, whose parent's inbox holds no
# submission n: it takes the move the Rust task runs on no fate
# (`owe.next`: submit under n) and so keeps owing k under n; to an open
# parent it submits one queued submission n, in front, and to a closing
# parent none (the task waits)
# EXCLUDES: a submission a closing parent admits, a first submission under
#   another id, not queued or not in front, a submission lost or doubled,
#   a report dropped before it was submitted
law child_owing_submits_once:
  for +cfg: Ch.Cfg
  for +k: Ch.Report
  for +n: Nat
  for +open: Bool
  for +inbox: List<&2, Ch.Sub>
  for +dt: Nat
  for +o: Ch.Obs
  for none: {chr_has(inbox, n) == False{} : Bool}
  {Ch.St.ph(Ch.step(cfg, Ch.St{Ch.Owing{k, n}, None{}, open, inbox}, Ch.Poll{dt, o})) == chr_moved(Ch.owe.next(None{}, n), k, n) : Ch.Ph} &
  {Ch.St.inbox(Ch.step(cfg, Ch.St{Ch.Owing{k, n}, None{}, open, inbox}, Ch.Poll{dt, o})) == chr_sent(open, n, inbox) : List<&2, Ch.Sub>}

# LAW child_owing_follows_its_submission (H5, S2): the step of a task that
# owes report k under id n, with no abort mark, whose newest submission n
# has fate f (whatever other ids stand before it in the inbox): it takes
# the move the Rust task runs on that fate (`owe.next`: queued, wait;
# withdrawn, owe it under n + 1; placed or read, end) and submits nothing
# EXCLUDES: a second submission while one is queued, a resubmission under
#   the same id, an end before the report is placed or read, the fate of
#   another id or of an older submission read, a submission changed by the
#   task's step
law child_owing_follows_its_submission:
  for +cfg: Ch.Cfg
  for +k: Ch.Report
  for +n: Nat
  for +open: Bool
  for +pre: List<&2, Ch.Sub>
  for +f: Ch.Fate
  for +rest: List<&2, Ch.Sub>
  for +dt: Nat
  for +o: Ch.Obs
  for newest: {chr_has(pre, n) == False{} : Bool}
  {Ch.St.ph(Ch.step(cfg, Ch.St{Ch.Owing{k, n}, None{}, open, List.append(&2, Ch.Sub, pre, Ch.Sub{n, f} <> rest)}, Ch.Poll{dt, o})) == chr_moved(Ch.owe.next(Some{f}, n), k, n) : Ch.Ph} &
  {Ch.St.inbox(Ch.step(cfg, Ch.St{Ch.Owing{k, n}, None{}, open, List.append(&2, Ch.Sub, pre, Ch.Sub{n, f} <> rest)}, Ch.Poll{dt, o})) == List.append(&2, Ch.Sub, pre, Ch.Sub{n, f} <> rest) : List<&2, Ch.Sub>}

# LAW child_ended_stays_ended (H5, S2): an ended task stays ended whatever
# happens next (any event, marked or not), and its step submits nothing
# EXCLUDES: an ended task that watches or owes again (a second report), a
#   submission after the end
law child_ended_stays_ended:
  for +cfg: Ch.Cfg
  for +cut: Maybe<&2, Bool>
  for +open: Bool
  for +inbox: List<&2, Ch.Sub>
  for +e: Ch.Ev
  for +dt: Nat
  for +o: Ch.Obs
  {Ch.St.ph(Ch.step(cfg, Ch.St{Ch.Ended{}, cut, open, inbox}, e)) == Ch.Ended{} : Ch.Ph} &
  {Ch.St.inbox(Ch.step(cfg, Ch.St{Ch.Ended{}, cut, open, inbox}, Ch.Poll{dt, o})) == inbox : List<&2, Ch.Sub>}

# LAW child_step_clears_the_mark (H5, S2): after the task's step no abort
# mark is left (it had none, or the step ran the abort), and the step
# leaves the parent as open as it was, in every state
# EXCLUDES: an abort mark kept after a step (an abort run again at every
#   step: the owed report never submitted), a mark invented by a step, a
#   task's step that opens or closes its parent
law child_step_clears_the_mark:
  for +cfg: Ch.Cfg
  for +s: Ch.St
  for +dt: Nat
  for +o: Ch.Obs
  {chr_cut(Ch.step(cfg, s, Ch.Poll{dt, o})) == None{} : Maybe<&2, Bool>} &
  {chr_open(Ch.step(cfg, s, Ch.Poll{dt, o})) == chr_open(s) : Bool}

# The abort
# ---------

# LAW child_abort_runs_at_the_next_step (H5, S3): a cancel (del false) or
# a delete only marks the task: its phase stays; the task's next step runs
# the abort the Rust task runs (`cut.ph`) on that phase, as a delete when
# this mark or one already there asked for a delete, submits nothing, and
# leaves no mark
# EXCLUDES: a cancel or delete that is forgotten, that moves the task
#   before its step or that withdraws or submits, a delete that a later
#   cancel turns into a cancel (no cancelled report), a cancel taken for a
#   delete, an abort that submits
law child_abort_runs_at_the_next_step:
  for +cfg: Ch.Cfg
  for +s: Ch.St
  for +del: Bool
  for +dt: Nat
  for +o: Ch.Obs
  {Ch.St.ph(Ch.step(cfg, s, Ch.Cut{del})) == Ch.St.ph(s) : Ch.Ph} &
  {Ch.St.ph(Ch.run([Ch.Cut{del}, Ch.Poll{dt, o}], cfg, s)) == Ch.cut.ph(Ch.St.ph(s), Bool.or(chr_deletes(chr_cut(s)), del)) : Ch.Ph} &
  {Ch.St.inbox(Ch.run([Ch.Cut{del}, Ch.Poll{dt, o}], cfg, s)) == Ch.St.inbox(s) : List<&2, Ch.Sub>} &
  {chr_cut(Ch.run([Ch.Cut{del}, Ch.Poll{dt, o}], cfg, s)) == None{} : Maybe<&2, Bool>}

# The parent's events
# -------------------

# LAW child_parent_never_moves_the_task (H5, S4): an event of the parent
# (a placement, a withdrawal, an abort, a close, a reopen, a read) changes
# neither the task's phase nor its abort mark, in every state
# EXCLUDES: a parent's event that ends, restarts or renumbers the owed
#   report, or that sets or clears an abort mark
law child_parent_never_moves_the_task:
  for +cfg: Ch.Cfg
  for +s: Ch.St
  for +e: Ch.Ev
  for parents: {chr_parents(e) == True{} : Bool}
  {Ch.St.ph(Ch.step(cfg, s, e)) == Ch.St.ph(s) : Ch.Ph} &
  {chr_cut(Ch.step(cfg, s, e)) == chr_cut(s) : Maybe<&2, Bool>}

# LAW child_only_close_and_reopen_set_openness (H5, S4): after a close the
# parent is closed and after a reopen it is open, in every state; a
# placement, a withdrawal, an abort, a read and a cancel or delete leave
# it as open as it was; a reopen changes no submission
# EXCLUDES: a close that leaves the parent open (a submission admitted
#   while it closes), a reopen that leaves it closed (the report never
#   submitted), another event that opens or closes it, a reopen that
#   settles or loses a submission
law child_only_close_and_reopen_set_openness:
  for +cfg: Ch.Cfg
  for +s: Ch.St
  for +m: Nat
  for +del: Bool
  {chr_open(Ch.step(cfg, s, Ch.Shut{})) == False{} : Bool} &
  {chr_open(Ch.step(cfg, s, Ch.Reopen{})) == True{} : Bool} &
  {chr_open(Ch.step(cfg, s, Ch.Deliver{m})) == chr_open(s) : Bool} &
  {chr_open(Ch.step(cfg, s, Ch.Withdraw{m})) == chr_open(s) : Bool} &
  {chr_open(Ch.step(cfg, s, Ch.Abort{})) == chr_open(s) : Bool} &
  {chr_open(Ch.step(cfg, s, Ch.Collect{})) == chr_open(s) : Bool} &
  {chr_open(Ch.step(cfg, s, Ch.Cut{del})) == chr_open(s) : Bool} &
  {Ch.St.inbox(Ch.step(cfg, s, Ch.Reopen{})) == Ch.St.inbox(s) : List<&2, Ch.Sub>}

# LAW child_parent_settles_each_alone (H5, S4): a placement, a withdrawal,
# an abort and a close settle each submission by itself, in place: the
# inbox xs ++ ys after the event is xs after it, then ys after it, in
# every state
# EXCLUDES: a submission lost, doubled, renumbered or moved by the
#   parent's event, one whose fate depends on the others in the inbox
law child_parent_settles_each_alone:
  for +cfg: Ch.Cfg
  for +ph: Ch.Ph
  for +cut: Maybe<&2, Bool>
  for +open: Bool
  for +xs: List<&2, Ch.Sub>
  for +ys: List<&2, Ch.Sub>
  for +m: Nat
  {chr_on(cfg, ph, cut, open, List.append(&2, Ch.Sub, xs, ys), Ch.Deliver{m}) == List.append(&2, Ch.Sub, chr_on(cfg, ph, cut, open, xs, Ch.Deliver{m}), chr_on(cfg, ph, cut, open, ys, Ch.Deliver{m})) : List<&2, Ch.Sub>} &
  {chr_on(cfg, ph, cut, open, List.append(&2, Ch.Sub, xs, ys), Ch.Withdraw{m}) == List.append(&2, Ch.Sub, chr_on(cfg, ph, cut, open, xs, Ch.Withdraw{m}), chr_on(cfg, ph, cut, open, ys, Ch.Withdraw{m})) : List<&2, Ch.Sub>} &
  {chr_on(cfg, ph, cut, open, List.append(&2, Ch.Sub, xs, ys), Ch.Abort{}) == List.append(&2, Ch.Sub, chr_on(cfg, ph, cut, open, xs, Ch.Abort{}), chr_on(cfg, ph, cut, open, ys, Ch.Abort{})) : List<&2, Ch.Sub>} &
  {chr_on(cfg, ph, cut, open, List.append(&2, Ch.Sub, xs, ys), Ch.Shut{}) == List.append(&2, Ch.Sub, chr_on(cfg, ph, cut, open, xs, Ch.Shut{}), chr_on(cfg, ph, cut, open, ys, Ch.Shut{})) : List<&2, Ch.Sub>}

# LAW child_parent_settles_the_named (H5, S4): the parent's run places the
# queued submission it names, its withdrawal withdraws the queued one it
# names, its abort and its close withdraw a queued one whatever its id
# EXCLUDES: a placement or withdrawal that leaves the named submission
#   queued (a report never delivered, a notice that still wakes the
#   parent), a placement that withdraws, a withdrawal that places, an
#   abort or a close that leaves a queued submission
law child_parent_settles_the_named:
  for +cfg: Ch.Cfg
  for +ph: Ch.Ph
  for +cut: Maybe<&2, Bool>
  for +open: Bool
  for +i: Nat
  {chr_on(cfg, ph, cut, open, [Ch.Sub{i, Ch.Queued{}}], Ch.Deliver{i}) == [Ch.Sub{i, Ch.Placed{}}] : List<&2, Ch.Sub>} &
  {chr_on(cfg, ph, cut, open, [Ch.Sub{i, Ch.Queued{}}], Ch.Withdraw{i}) == [Ch.Sub{i, Ch.Withdrawn{}}] : List<&2, Ch.Sub>} &
  {chr_on(cfg, ph, cut, open, [Ch.Sub{i, Ch.Queued{}}], Ch.Abort{}) == [Ch.Sub{i, Ch.Withdrawn{}}] : List<&2, Ch.Sub>} &
  {chr_on(cfg, ph, cut, open, [Ch.Sub{i, Ch.Queued{}}], Ch.Shut{}) == [Ch.Sub{i, Ch.Withdrawn{}}] : List<&2, Ch.Sub>}

# LAW child_parent_spares_the_unnamed (H5, S4): a placement or a
# withdrawal of the id m leaves a queued submission with another id i
# queued
# EXCLUDES: a placement or a withdrawal that settles a submission it does
#   not name (another report's notice placed or pulled)
law child_parent_spares_the_unnamed:
  for +cfg: Ch.Cfg
  for +ph: Ch.Ph
  for +cut: Maybe<&2, Bool>
  for +open: Bool
  for +i: Nat
  for +m: Nat
  for other: {Nat.is_eq(i, m) == False{} : Bool}
  {chr_on(cfg, ph, cut, open, [Ch.Sub{i, Ch.Queued{}}], Ch.Deliver{m}) == [Ch.Sub{i, Ch.Queued{}}] : List<&2, Ch.Sub>} &
  {chr_on(cfg, ph, cut, open, [Ch.Sub{i, Ch.Queued{}}], Ch.Withdraw{m}) == [Ch.Sub{i, Ch.Queued{}}] : List<&2, Ch.Sub>}

# LAW child_settled_stays_settled (H5, S4): each submission settles once:
# one that is withdrawn, placed or read stays as it is through every
# placement, withdrawal, abort and close, whatever id they name (a
# withdrawal that loses the race to a placement leaves it placed)
# EXCLUDES: a placed report withdrawn again (lost after the task ended), a
#   withdrawn one placed (the report twice in the transcript once its
#   resubmission is placed), a read one placed or queued again
law child_settled_stays_settled:
  for +cfg: Ch.Cfg
  for +ph: Ch.Ph
  for +cut: Maybe<&2, Bool>
  for +open: Bool
  for +i: Nat
  for +f: Ch.Fate
  for +m: Nat
  for settled: {chr_settled(f) == True{} : Bool}
  {chr_on(cfg, ph, cut, open, [Ch.Sub{i, f}], Ch.Deliver{m}) == [Ch.Sub{i, f}] : List<&2, Ch.Sub>} &
  {chr_on(cfg, ph, cut, open, [Ch.Sub{i, f}], Ch.Withdraw{m}) == [Ch.Sub{i, f}] : List<&2, Ch.Sub>} &
  {chr_on(cfg, ph, cut, open, [Ch.Sub{i, f}], Ch.Abort{}) == [Ch.Sub{i, f}] : List<&2, Ch.Sub>} &
  {chr_on(cfg, ph, cut, open, [Ch.Sub{i, f}], Ch.Shut{}) == [Ch.Sub{i, f}] : List<&2, Ch.Sub>}

# The parent's read
# -----------------

# LAW child_read_reads_the_owed_report (H5, S5): the parent's read changes
# nothing while the child is watched (no report yet) or the task ended
# (none left); of a report owed under n whose newest submission is n, it
# reads that submission when queued (the read withdraws the notice) or
# withdrawn, leaves it placed when placed (the read lost the race to the
# placement) and read when read; the older submissions stay
# EXCLUDES: a read that leaves the queued notice in the inbox (the parent
#   woken for what it read), a read that unplaces a placed report, a read
#   counted for a watched child or an ended task, a read that touches
#   another submission
law child_read_reads_the_owed_report:
  for +cfg: Ch.Cfg
  for +w: Ch.W
  for +k: Ch.Report
  for +n: Nat
  for +cut: Maybe<&2, Bool>
  for +open: Bool
  for +inbox: List<&2, Ch.Sub>
  {chr_on(cfg, Ch.Watching{w}, cut, open, inbox, Ch.Collect{}) == inbox : List<&2, Ch.Sub>} &
  {chr_on(cfg, Ch.Ended{}, cut, open, inbox, Ch.Collect{}) == inbox : List<&2, Ch.Sub>} &
  {chr_on(cfg, Ch.Owing{k, n}, cut, open, Ch.Sub{n, Ch.Queued{}} <> inbox, Ch.Collect{}) == Ch.Sub{n, Ch.Read{}} <> inbox : List<&2, Ch.Sub>} &
  {chr_on(cfg, Ch.Owing{k, n}, cut, open, Ch.Sub{n, Ch.Withdrawn{}} <> inbox, Ch.Collect{}) == Ch.Sub{n, Ch.Read{}} <> inbox : List<&2, Ch.Sub>} &
  {chr_on(cfg, Ch.Owing{k, n}, cut, open, Ch.Sub{n, Ch.Placed{}} <> inbox, Ch.Collect{}) == Ch.Sub{n, Ch.Placed{}} <> inbox : List<&2, Ch.Sub>} &
  {chr_on(cfg, Ch.Owing{k, n}, cut, open, Ch.Sub{n, Ch.Read{}} <> inbox, Ch.Collect{}) == Ch.Sub{n, Ch.Read{}} <> inbox : List<&2, Ch.Sub>}

# LAW child_read_stands_for_a_missing_submission (H5, S5): the parent's
# read of a report owed under n whose newest submission is not n (or that
# has none): a read submission n stands in front of the inbox, and every
# submission stays as it was
# EXCLUDES: a read of a report not yet submitted that is lost (the task
#   then submits what the parent already read), a read that replaces or
#   settles the newest submission of another id
law child_read_stands_for_a_missing_submission:
  for +cfg: Ch.Cfg
  for +k: Ch.Report
  for +n: Nat
  for +cut: Maybe<&2, Bool>
  for +open: Bool
  for +inbox: List<&2, Ch.Sub>
  for missing: {chr_newest_is(inbox, n) == False{} : Bool}
  {chr_on(cfg, Ch.Owing{k, n}, cut, open, inbox, Ch.Collect{}) == Ch.Sub{n, Ch.Read{}} <> inbox : List<&2, Ch.Sub>}
