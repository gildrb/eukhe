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
#   request id n; the parent knows each id once. The parent's inbox holds
#   every submission: its run places queued ones, an abort, a close or a
#   withdrawal of one input withdraws them, and each settles once (a
#   withdrawal that loses the race to a placement leaves it placed). The
#   task reads its submission's fate: placed ends it, withdrawn has it
#   submit again under n + 1. A closing parent admits no submission.
# - An abort of the task (`Cut`) submits nothing: the report it owes (a
#   delete owes a cancelled report) goes on under the same rule.
#
# LAWS.bend states what must hold (section H5); PROOF.bend proves it with
# PROOF.bend section child. The Rust task runs `verdict`, `owe.next` and
# `cut.ph` as the compiled Bend core (bend/ffi_child.bend).

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

def W.left(w: W) -> Nat:
  match w:
    case W{t, l, n}:
      l

def W.tries(w: W) -> Nat:
  match w:
    case W{t, l, n}:
      n

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

def Next.watching(x: Next) -> Bool:
  match x:
    case Watch{w}:
      True{}
    case Owe{k}:
      False{}
    case Quiet{}:
      False{}

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

# Quiet polls
# -----------
# A poll that shows no progress: the child unsettled with the token the
# watch already holds, or a failed poll. Each takes 1 + dt ms (the Rust
# watch sleeps a poll interval between polls).

type Hush is Data:
  Same{dt: Nat}
  Miss{dt: Nat}

def Hush.look(+cfg: Cfg, +w: W, h: Hush) -> Next:
  match h:
    case Same{dt}:
      look(cfg, w, 1n+dt, Busy{W.tok(w)})
    case Miss{dt}:
      look(cfg, w, 1n+dt, Lost{})

# one more quiet poll, if the watch still runs
def hush.step(+cfg: Cfg, h: Hush, x: Next) -> Next:
  match x:
    case Watch{w}:
      Hush.look(cfg, w, h)
    case Owe{k}:
      Owe{k}
    case Quiet{}:
      Quiet{}

# the verdict after the quiet polls hs, from verdict x
def hush(hs: List<&2, Hush>, +cfg: Cfg, x: Next) -> Next:
  match hs:
    case Nil{}:
      x
    case h <> t:
      hush(t, cfg, hush.step(cfg, h, x))

# The task
# --------

# a submission's fate in the parent's inbox
type Fate is Data:
  Queued{}
  Withdrawn{}
  Placed{}

# one submission of the report: its id (1, 2, ...) and fate
type Sub is Data:
  Sub{id: Nat, fate: Fate}

# watching the child, owing report k under id n, or ended
type Ph is Data:
  Watching{w: W}
  Owing{k: Report, n: Nat}
  Ended{}

# ph: the task's phase; cut: the task's abort mark (Some{delete}); open:
# the parent is open; inbox: the parent's submissions of the report,
# newest first
type St is Data:
  St{ph: Ph, cut: Maybe<&2, Bool>, open: Bool, inbox: List<&2, Sub>}

def St.init(+cfg: Cfg) -> St:
  St{Watching{W.fresh(cfg, None{})}, None{}, True{}, Nil{}}

def St.ph(s: St) -> Ph:
  match s:
    case St{ph, c, o, i}:
      ph

def St.inbox(s: St) -> List<&2, Sub>:
  match s:
    case St{ph, c, o, i}:
      i

# the id the task's report goes under (0 when it owes none)
def St.owed(s: St) -> Nat:
  match s:
    case St{ph, c, o, i}:
      match ph:
        case Watching{w}:
          0n
        case Owing{k, n}:
          n
        case Ended{}:
          0n

def Ph.owing(ph: Ph) -> Bool:
  match ph:
    case Watching{w}:
      False{}
    case Owing{k, n}:
      True{}
    case Ended{}:
      False{}

# The parent's inbox
# ------------------
# What the parent does to its queued submissions: its run places one (m),
# it withdraws one (m), or an abort or a close withdraws them all. A
# settled submission stays as it settled: a withdrawal that loses the race
# to a placement leaves it placed.

type Act is Data:
  Place{m: Nat}
  Pull{m: Nat}
  PullAll{}

def Act.hit(hit: Bool, f: Fate) -> Fate:
  match hit:
    case True{}:
      f
    case False{}:
      Queued{}

# the act on the queued submission with id i
def Act.queued(a: Act, +i: Nat) -> Fate:
  match a:
    case Place{m}:
      Act.hit(Nat.is_eq(i, m), Placed{})
    case Pull{m}:
      Act.hit(Nat.is_eq(i, m), Withdrawn{})
    case PullAll{}:
      Withdrawn{}

def Fate.act(a: Act, +i: Nat, f: Fate) -> Fate:
  match f:
    case Queued{}:
      Act.queued(a, i)
    case Withdrawn{}:
      Withdrawn{}
    case Placed{}:
      Placed{}

def act(inbox: List<&2, Sub>, +a: Act) -> List<&2, Sub>:
  match inbox:
    case Nil{}:
      Nil{}
    case s <> rest:
      match s:
        case Sub{+i, f}:
          Sub{i, Fate.act(a, i, f)} <> act(rest, a)

def fate.here(same: Bool, f: Fate) -> Maybe<&2, Fate>:
  match same:
    case True{}:
      Some{f}
    case False{}:
      None{}

# the fate of the submission with id n, if the parent has one (the Rust
# harness finds a submission by its request id)
def fate(inbox: List<&2, Sub>, +n: Nat) -> Maybe<&2, Fate>:
  match inbox:
    case Nil{}:
      None{}
    case s <> rest:
      match s:
        case Sub{+i, f}:
          Maybe.or(&2, Fate, fate.here(Nat.is_eq(i, n), f), fate(rest, n))

# The one report rule, on the fate of submission n of report k: none yet,
# submit it (a closing parent admits none: the task waits); queued, wait;
# withdrawn, owe the report under n + 1 (the Rust report phase commits the
# next id, and its next invocation submits it); placed, end.
def owe.new(open: Bool, k: Report, +n: Nat, inbox: List<&2, Sub>) -> St:
  match open:
    case True{}:
      St{Owing{k, n}, None{}, True{}, Sub{n, Queued{}} <> inbox}
    case False{}:
      St{Owing{k, n}, None{}, False{}, inbox}

def owe(f: Maybe<&2, Fate>, k: Report, +n: Nat, open: Bool, inbox: List<&2, Sub>) -> St:
  match f:
    case None{}:
      owe.new(open, k, n, inbox)
    case Some{x}:
      match x:
        case Queued{}:
          St{Owing{k, n}, None{}, open, inbox}
        case Withdrawn{}:
          St{Owing{k, 1n+n}, None{}, open, inbox}
        case Placed{}:
          St{Ended{}, None{}, open, inbox}

# The abort submits nothing: an owed report (a delete owes a cancelled
# one) goes on to a new task in the report phase under the same ids,
# which the abort does not reach; the model keeps it as this task, its
# mark cleared. A plain cancel of a watched child owes nothing.
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

# the watch phase's next phase
def watched(x: Next) -> Ph:
  match x:
    case Watch{w}:
      Watching{w}
    case Owe{k}:
      Owing{k, 1n}
    case Quiet{}:
      Ended{}

# the task's step with no abort mark
def task.run(+cfg: Cfg, ph: Ph, open: Bool, +inbox: List<&2, Sub>, +dt: Nat, o: Obs) -> St:
  match ph:
    case Watching{w}:
      St{watched(look(cfg, w, 1n+dt, o)), None{}, open, inbox}
    case Owing{k, +n}:
      owe(fate(inbox, n), k, n, open, inbox)
    case Ended{}:
      St{Ended{}, None{}, open, inbox}

# the task's step: an abort mark runs the abort; a closing parent stops
# only its submissions
def task(+cfg: Cfg, ph: Ph, cut: Maybe<&2, Bool>, open: Bool, +inbox: List<&2, Sub>, +dt: Nat, o: Obs) -> St:
  match cut:
    case None{}:
      task.run(cfg, ph, open, inbox, dt, o)
    case Some{del}:
      St{cut.ph(ph, del), None{}, open, inbox}

# the abort mark after a cancel (del false) or a delete: a delete stays
# (the Rust abort reads the row's deletion when it runs)
def mark(cut: Maybe<&2, Bool>, del: Bool) -> Maybe<&2, Bool>:
  match cut:
    case None{}:
      Some{del}
    case Some{d}:
      Some{Bool.or(d, del)}

# the parent's events, and the task's next step (a poll that reads o in
# the watch phase)
type Ev is Data:
  Poll{dt: Nat, o: Obs}
  Deliver{m: Nat}
  Withdraw{m: Nat}
  Abort{}
  Shut{}
  Reopen{}
  Cut{del: Bool}

def step(+cfg: Cfg, s: St, e: Ev) -> St:
  match s:
    case St{ph, cut, open, +inbox}:
      match e:
        case Poll{dt, o}:
          task(cfg, ph, cut, open, inbox, dt, o)
        case Deliver{m}:
          St{ph, cut, open, act(inbox, Place{m})}
        case Withdraw{m}:
          St{ph, cut, open, act(inbox, Pull{m})}
        case Abort{}:
          St{ph, cut, open, act(inbox, PullAll{})}
        case Shut{}:
          St{ph, cut, False{}, act(inbox, PullAll{})}
        case Reopen{}:
          St{ph, cut, True{}, inbox}
        case Cut{del}:
          St{ph, mark(cut, del), open, inbox}

def run(evs: List<&2, Ev>, +cfg: Cfg, s: St) -> St:
  match evs:
    case Nil{}:
      s
    case e <> t:
      run(t, cfg, step(cfg, s, e))

# What the laws count
# -------------------

def Fate.placed(f: Fate) -> Nat:
  match f:
    case Queued{}:
      0n
    case Withdrawn{}:
      0n
    case Placed{}:
      1n

def Fate.live(f: Fate) -> Nat:
  match f:
    case Queued{}:
      1n
    case Withdrawn{}:
      0n
    case Placed{}:
      1n

# the report's entries in the parent's transcript: its placed submissions
def placed(inbox: List<&2, Sub>) -> Nat:
  match inbox:
    case Nil{}:
      0n
    case s <> rest:
      match s:
        case Sub{i, f}:
          Nat.add(Fate.placed(f), placed(rest))

# the submissions that are queued or placed
def live(inbox: List<&2, Sub>) -> Nat:
  match inbox:
    case Nil{}:
      0n
    case s <> rest:
      match s:
        case Sub{i, f}:
          Nat.add(Fate.live(f), live(rest))

def St.placed(s: St) -> Nat:
  placed(St.inbox(s))

def Ev.cut(e: Ev) -> Nat:
  match e:
    case Poll{dt, o}:
      0n
    case Deliver{m}:
      0n
    case Withdraw{m}:
      1n
    case Abort{}:
      1n
    case Shut{}:
      1n
    case Reopen{}:
      0n
    case Cut{d}:
      0n

# the parent's withdrawals: aborts, closes, withdrawals of one input
def cuts(evs: List<&2, Ev>) -> Nat:
  match evs:
    case Nil{}:
      0n
    case e <> t:
      Nat.add(cuts(t), Ev.cut(e))

# failed polls that took 1 + d ms each
def misses(ds: List<&2, Nat>) -> List<&2, Hush>:
  match ds:
    case Nil{}:
      Nil{}
    case d <> t:
      Miss{d} <> misses(t)

# the clock is at most full
def within(+cfg: Cfg, x: Next) -> Bool:
  match x:
    case Watch{+w}:
      Bool.and(Nat.is_le(W.left(w), Cfg.stall(cfg)), Nat.is_le(W.tries(w), Cfg.fails(cfg)))
    case Owe{k}:
      True{}
    case Quiet{}:
      True{}

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

def Call.reports(c: Call) -> Bool:
  match c:
    case Watches{w}:
      False{}
    case Reports{k}:
      True{}
    case Settles{why}:
      False{}

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

# the task after move mv of report k owed under n (a closing parent's
# inbox admits no submission)
def owe.do(mv: Move, k: Report, +n: Nat, open: Bool, inbox: List<&2, Sub>) -> St:
  match mv:
    case Submit{m}:
      owe.new(open, k, m, inbox)
    case Await{}:
      St{Owing{k, n}, None{}, open, inbox}
    case Resubmit{m}:
      St{Owing{k, m}, None{}, open, inbox}
    case Delivered{}:
      St{Ended{}, None{}, open, inbox}
