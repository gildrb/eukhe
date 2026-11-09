# child: the life of one subagent as its parent's durable task sees it
# (docs/harness.md H5). The Rust code is the `eukhe.rlm.child` task
# (crates/eukhe-core/src/durable/children/task.rs) and its watch verdict
# (children/watch.rs).
#
# - The watch polls the child. A poll reads the child unsettled (running,
#   or idle with background jobs) with its progress token, or settled
#   (answered, failed, gone), or fails (the probe got no answer).
# - The watch's clock (`W`) counts down two things: `left`, the ms of no
#   progress the child may still show before it is stalled, and `tries`,
#   the failed polls in a row before it is unreachable. A poll whose token
#   is new (progress) sets both back to full.
# - Then the task owes one report. It submits it to the parent under
#   request id n; the parent knows each id once. The task reads its
#   submission's fate: placed ends it, withdrawn has it submit again
#   under n + 1.
# - An abort of the task submits nothing: the report it owes (a delete
#   owes a cancelled report) goes on under the same rule.
#
# This file holds only what the Rust task runs, as the compiled Bend core
# (bend/ffi_child.bend): `verdict`, `owe.next` and `cut.ph`. LAWS.bend
# states what must hold (section H5), running them in the environment of
# spec/child.bend (the parent's inbox, the task's steps); PROOF.bend
# proves it with proof/child/.

import Base

# Settings
# --------

# stall: subagentStallMs; fails: CHILD_POLL_FAILURES
type Cfg is Data:
  Cfg{stall: Nat, fails: Nat}

def Cfg.stall(c: Cfg) -> Nat:
  match c:
    case Cfg{s, f}:
      s

def Cfg.fails(c: Cfg) -> Nat:
  match c:
    case Cfg{s, f}:
      f

# The watch
# ---------

# tok: the child's last progress token; left: ms of no progress left
# before a stall; tries: failed polls in a row left before unreachable
type W is Data:
  W{tok: Maybe<&2, Nat>, left: Nat, tries: Nat}

def W.tok(w: W) -> Maybe<&2, Nat>:
  match w:
    case W{t, l, n}:
      t

# a full clock after progress to token t
def W.fresh(+cfg: Cfg, t: Maybe<&2, Nat>) -> W:
  W{t, Cfg.stall(cfg), Cfg.fails(cfg)}

# what one poll read
type Obs is Data:
  Busy{tok: Maybe<&2, Nat>}
  Lost{}
  Answered{replied: Bool}
  Broke{}
  Gone{}

# what the parent is told
type Report is Data:
  Completed{}
  Failed{}
  Cancelled{}
  Stalled{}
  Unreachable{}

# the watch's verdict: watch on, owe a report, or end without one (the
# child already replied to its parent)
type Next is Data:
  Watch{w: W}
  Owe{k: Report}
  Quiet{}

# whether token t is progress after tok
def moved.some(tok: Maybe<&2, Nat>, +x: Nat) -> Bool:
  match tok:
    case None{}:
      True{}
    case Some{y}:
      Bool.not(Nat.is_eq(y, x))

def moved(tok: Maybe<&2, Nat>, t: Maybe<&2, Nat>) -> Bool:
  match t:
    case None{}:
      False{}
    case Some{x}:
      moved.some(tok, x)

# a poll without progress: `rest` ms are left; none left is a stall
def spend(rest: Nat, tok: Maybe<&2, Nat>, tries: Nat) -> Next:
  match rest:
    case 0n:
      Owe{Stalled{}}
    case 1n+p:
      Watch{W{tok, 1n+p, tries}}

# a failed poll that took e ms
def lost(w: W, +e: Nat) -> Next:
  match w:
    case W{tok, left, tries}:
      match tries:
        case 0n:
          Owe{Unreachable{}}
        case 1n+p:
          match p:
            case 0n:
              Owe{Unreachable{}}
            case 1n+q:
              spend(Nat.sub(left, e), tok, 1n+q)

# an unsettled child, `news` when its token t moved
def busy(news: Bool, +cfg: Cfg, w: W, t: Maybe<&2, Nat>, +e: Nat) -> Next:
  match news:
    case True{}:
      Watch{W.fresh(cfg, t)}
    case False{}:
      match w:
        case W{tok, left, tries}:
          spend(Nat.sub(left, e), tok, Cfg.fails(cfg))

def settled(replied: Bool) -> Next:
  match replied:
    case True{}:
      Quiet{}
    case False{}:
      Owe{Completed{}}

# the watch's verdict on one poll that read o and took e ms since the last
def look(+cfg: Cfg, +w: W, +e: Nat, o: Obs) -> Next:
  match o:
    case Busy{+t}:
      busy(moved(W.tok(w), t), cfg, w, t, e)
    case Lost{}:
      lost(w, e)
    case Answered{r}:
      settled(r)
    case Broke{}:
      Owe{Failed{}}
    case Gone{}:
      Owe{Failed{}}

# The report
# ----------

# a submission's fate in the parent's inbox
type Fate is Data:
  Queued{}
  Withdrawn{}
  Placed{}

# watching the child, owing report k under id n, or ended
type Ph is Data:
  Watching{w: W}
  Owing{k: Report, n: Nat}
  Ended{}

# The abort submits nothing: an owed report (a delete owes a cancelled
# one) goes on to a new task in the report phase under the same ids,
# which the abort does not reach. A plain cancel of a watched child owes
# nothing.
def cut.ph(ph: Ph, del: Bool) -> Ph:
  match ph:
    case Watching{w}:
      match del:
        case True{}:
          Owing{Cancelled{}, 1n}
        case False{}:
          Ended{}
    case Owing{k, n}:
      Owing{k, n}
    case Ended{}:
      Ended{}

# The task's decisions
# --------------------
# The Rust task runs these as the compiled Bend core: the verdict on one
# poll of the watch phase (`verdict`), the report phase's move on the
# fate of its submission (`owe.next`) and the abort (`cut.ph`).

# where a settled child's outcome goes: a report in the parent's inbox,
# or nowhere (a silent task only settles the child's row)
type Mode is Data:
  Inbox{}
  Silent{}

# what the task does after one poll: watch on with clock w, report k to
# the parent, or end with no report (why: the report a silent task does
# not send; None when the child already replied to its parent)
type Call is Data:
  Watches{w: W}
  Reports{k: Report}
  Settles{why: Maybe<&2, Report>}

def call.owe(m: Mode, k: Report) -> Call:
  match m:
    case Inbox{}:
      Reports{k}
    case Silent{}:
      Settles{Some{k}}

def call.of(x: Next, m: Mode) -> Call:
  match x:
    case Watch{w}:
      Watches{w}
    case Owe{k}:
      call.owe(m, k)
    case Quiet{}:
      Settles{None{}}

# the task's call on one poll that read o and took e ms since the last,
# in mode m
def verdict(+cfg: Cfg, +w: W, +e: Nat, o: Obs, m: Mode) -> Call:
  call.of(look(cfg, w, e, o), m)

# the report phase's move on the fate of submission n of its report
type Move is Data:
  Submit{n: Nat}
  Await{}
  Resubmit{n: Nat}
  Delivered{}

def owe.next.fate(x: Fate, +n: Nat) -> Move:
  match x:
    case Queued{}:
      Await{}
    case Withdrawn{}:
      Resubmit{1n+n}
    case Placed{}:
      Delivered{}

# none yet: submit it under n; queued: wait; withdrawn: owe it under
# n + 1; placed: end
def owe.next(f: Maybe<&2, Fate>, +n: Nat) -> Move:
  match f:
    case None{}:
      Submit{n}
    case Some{x}:
      owe.next.fate(x, n)
