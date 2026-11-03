# eukhe: the laws of area child: the task's step and run
#
# Ch.step moves the task and the parent's inbox on one event and Ch.run
# folds the events of a history; the H5 report laws of laws/child.bend
# (child_one_live, child_report_once, child_resubmits_per_abort,
# child_delivered_once) read Ch.run. These laws pin the step and the run,
# for every setting, state and history, to the rule restated here: the
# watch's verdict is K1's (ch_look_spec), an abort leaves ChildAbort's
# phase, an owed report moves by the one report rule (ChildMove carried
# out), and the parent's events settle its queued submissions.

import Base
import ../../bend/child.bend as Ch
import ../child.bend as Child

# The parent's inbox
# ------------------

# the fate of the queued submission with id i that act a reaches (b: a
# names i): fate f when it does, else it stays queued
def chr_hit(b: Bool, f: Ch.Fate) -> Ch.Fate:
  match b:
    case True{}:
      f
    case False{}:
      Ch.Queued{}

# the fate f of submission i after act a: a queued one is placed when a
# places i, withdrawn when a withdraws i or every submission, else stays
# queued; a withdrawn, placed or read one stays as it settled
def chr_settle(f: Ch.Fate, a: Ch.Act, +i: Nat) -> Ch.Fate:
  match f:
    case Ch.Queued{}:
      match a:
        case Ch.Place{m}:
          chr_hit(Nat.is_eq(i, m), Ch.Placed{})
        case Ch.Pull{m}:
          chr_hit(Nat.is_eq(i, m), Ch.Withdrawn{})
        case Ch.PullAll{}:
          Ch.Withdrawn{}
    case Ch.Withdrawn{}:
      Ch.Withdrawn{}
    case Ch.Placed{}:
      Ch.Placed{}
    case Ch.Read{}:
      Ch.Read{}

# the inbox xs (newest first) after act a: each submission keeps its id
# and place, its fate settled by a
def chr_inbox(xs: List<&2, Ch.Sub>, +a: Ch.Act) -> List<&2, Ch.Sub>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> r:
      match x:
        case Ch.Sub{+i, f}:
          Ch.Sub{i, chr_settle(f, a, i)} <> chr_inbox(r, a)

# the fate f of the submission at hand when it is the one sought (b), else
# the fate found further on (x)
def chr_here(b: Bool, f: Ch.Fate, x: Maybe<&2, Ch.Fate>) -> Maybe<&2, Ch.Fate>:
  match b:
    case True{}:
      Some{f}
    case False{}:
      x

# the fate of the newest submission with id n in xs, if any
def chr_find(xs: List<&2, Ch.Sub>, +n: Nat) -> Maybe<&2, Ch.Fate>:
  match xs:
    case Nil{}:
      None{}
    case x <> r:
      match x:
        case Ch.Sub{+i, f}:
          chr_here(Nat.is_eq(i, n), f, chr_find(r, n))

# the parent's read of report n, on the inbox xs (newest first): the
# newest submission, when it is n, is read unless it was placed (a queued
# one is withdrawn for the read); else a read submission n stands newest
def chr_read.fate(f: Ch.Fate) -> Ch.Fate:
  match f:
    case Ch.Queued{}:
      Ch.Read{}
    case Ch.Withdrawn{}:
      Ch.Read{}
    case Ch.Placed{}:
      Ch.Placed{}
    case Ch.Read{}:
      Ch.Read{}

def chr_read.at(same: Bool, +n: Nat, +i: Nat, f: Ch.Fate, r: List<&2, Ch.Sub>) -> List<&2, Ch.Sub>:
  match same:
    case True{}:
      Ch.Sub{i, chr_read.fate(f)} <> r
    case False{}:
      Ch.Sub{n, Ch.Read{}} <> Ch.Sub{i, f} <> r

def chr_read.sub(xs: List<&2, Ch.Sub>, +n: Nat) -> List<&2, Ch.Sub>:
  match xs:
    case Nil{}:
      [Ch.Sub{n, Ch.Read{}}]
    case x <> r:
      match x:
        case Ch.Sub{+i, f}:
          chr_read.at(Nat.is_eq(i, n), n, i, f, r)

# the parent reads the settled child: only an owed report is read
def chr_read(ph: Ch.Ph, +xs: List<&2, Ch.Sub>) -> List<&2, Ch.Sub>:
  match ph:
    case Ch.Watching{w}:
      xs
    case Ch.Owing{k, +n}:
      chr_read.sub(xs, n)
    case Ch.Ended{}:
      xs

# The task
# --------

# the abort mark after a cancel (del false) or a delete: none becomes del;
# a delete marked stays marked
def chr_mark(cut: Maybe<&2, Bool>, del: Bool) -> Maybe<&2, Bool>:
  match cut:
    case None{}:
      Some{del}
    case Some{d}:
      Some{Bool.or(d, del)}

# the watch phase's next phase on K1's verdict x: watch on; owe report k
# under the first id (1); a child that replied ends the task
def chr_watched(x: Ch.Next) -> Ch.Ph:
  match x:
    case Ch.Watch{w}:
      Ch.Watching{w}
    case Ch.Owe{k}:
      Ch.Owing{k, 1n}
    case Ch.Quiet{}:
      Ch.Ended{}

# the one report rule (ChildMove carried out) on the fate f of submission
# n of report k: none yet, submit it under n queued (a closing parent
# admits none: the task waits under n); queued, wait under n; withdrawn,
# owe it under n + 1; placed or read, end. The mark is clear after the
# step.
def chr_owe(f: Maybe<&2, Ch.Fate>, k: Ch.Report, +n: Nat, open: Bool, inbox: List<&2, Ch.Sub>) -> Ch.St:
  match f:
    case None{}:
      match open:
        case True{}:
          Ch.St{Ch.Owing{k, n}, None{}, True{}, Ch.Sub{n, Ch.Queued{}} <> inbox}
        case False{}:
          Ch.St{Ch.Owing{k, n}, None{}, False{}, inbox}
    case Some{x}:
      match x:
        case Ch.Queued{}:
          Ch.St{Ch.Owing{k, n}, None{}, open, inbox}
        case Ch.Withdrawn{}:
          Ch.St{Ch.Owing{k, 1n+n}, None{}, open, inbox}
        case Ch.Placed{}:
          Ch.St{Ch.Ended{}, None{}, open, inbox}
        case Ch.Read{}:
          Ch.St{Ch.Ended{}, None{}, open, inbox}

# the task's step on a poll that read o, 1 + dt ms after the last: an
# abort mark runs the abort (ChildAbort's phase, the mark cleared); else a
# watched child gets K1's verdict, an owed report the report rule on its
# submission's fate, an ended task stays ended (the mark clear); the
# parent's openness and inbox stay
def chr_poll(+cfg: Ch.Cfg, cut: Maybe<&2, Bool>, ph: Ch.Ph, open: Bool, +inbox: List<&2, Ch.Sub>, +dt: Nat, o: Ch.Obs) -> Ch.St:
  match cut:
    case Some{del}:
      Ch.St{Child.ChildAbort(ph, del), None{}, open, inbox}
    case None{}:
      match ph:
        case Ch.Watching{w}:
          Ch.St{chr_watched(Child.ch_look_spec(cfg, w, 1n+dt, o)), None{}, open, inbox}
        case Ch.Owing{k, +n}:
          chr_owe(chr_find(inbox, n), k, n, open, inbox)
        case Ch.Ended{}:
          Ch.St{Ch.Ended{}, None{}, open, inbox}

# one event: a poll steps the task; the parent places or withdraws one
# submission, aborts (withdraws every queued one), closes (the same, and
# admits none), reopens, or reads the owed report itself; a cancel or
# delete marks the task for an abort
def chr_step(+cfg: Ch.Cfg, s: Ch.St, e: Ch.Ev) -> Ch.St:
  match s:
    case Ch.St{+ph, cut, open, +inbox}:
      match e:
        case Ch.Poll{dt, o}:
          chr_poll(cfg, cut, ph, open, inbox, dt, o)
        case Ch.Deliver{m}:
          Ch.St{ph, cut, open, chr_inbox(inbox, Ch.Place{m})}
        case Ch.Withdraw{m}:
          Ch.St{ph, cut, open, chr_inbox(inbox, Ch.Pull{m})}
        case Ch.Abort{}:
          Ch.St{ph, cut, open, chr_inbox(inbox, Ch.PullAll{})}
        case Ch.Shut{}:
          Ch.St{ph, cut, False{}, chr_inbox(inbox, Ch.PullAll{})}
        case Ch.Reopen{}:
          Ch.St{ph, cut, True{}, inbox}
        case Ch.Cut{del}:
          Ch.St{ph, chr_mark(cut, del), open, inbox}
        case Ch.Collect{}:
          Ch.St{ph, cut, open, chr_read(ph, inbox)}

# the spec's run: the spec's step on each event of evs, oldest first, from s
def chr_run(evs: List<&2, Ch.Ev>, +cfg: Ch.Cfg, s: Ch.St) -> Ch.St:
  match evs:
    case Nil{}:
      s
    case e <> r:
      chr_run(r, cfg, chr_step(cfg, s, e))

# LAW child_step_exact (H5): on every setting and state, the task's step on every event is the rule's: a poll runs a pending abort (ChildAbort), else K1's verdict on a watched child, the one report rule on an owed report's submission, or nothing on an ended task, and clears the mark; the parent's placement, withdrawal, abort and close settle exactly its queued submissions they name, a close and a reopen set its openness, its read reads the owed report alone; a cancel or delete marks the task
# EXCLUDES: a step that loses, invents or renumbers a submission, settles
#   one twice or one it does not name, submits while one is queued or to a
#   closing parent, resubmits under the same id, keeps an abort mark after
#   a poll or forgets one, a watched child's phase other than K1's verdict
law child_step_exact:
  for +cfg: Ch.Cfg
  for +s: Ch.St
  for e: Ch.Ev
  {Ch.step(cfg, s, e) == chr_step(cfg, s, e) : Ch.St}

# LAW child_run_exact (H5): on every setting and state, the task's run of every history is the rule's step on each event, one at a time, oldest first
# EXCLUDES: a run that drops, repeats, reorders or invents events (the run
#   that keeps its state, `run(evs, cfg, s) = s`, which passed every H5
#   report law: the initial state owes nothing and holds no submission), a
#   run that ignores the state it starts from
law child_run_exact:
  for evs: List<&2, Ch.Ev>
  for +cfg: Ch.Cfg
  for +s: Ch.St
  {Ch.run(evs, cfg, s) == chr_run(evs, cfg, s) : Ch.St}
