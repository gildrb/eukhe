# child (spec): what the laws of area child (laws/child.bend, H5 in
# docs/harness.md) run the shipped decisions of bend/child.bend in. A
# spec: the shipped code never calls it.
#
# - Quiet polls: a run of polls that show no progress (the child
#   unsettled with the token the watch holds, or a failed poll), each
#   decided by the shipped `look`.
# - The parent's side of one child task: the parent's inbox (every
#   submission of the report, each queued, withdrawn or placed; its run
#   places one, it withdraws one, an abort or a close withdraws them all;
#   a withdrawal that loses the race to a placement leaves it placed) and
#   the task's steps around the three decisions the Rust task runs as the
#   compiled Bend core (bend/ffi_child.bend): `verdict` on a poll of the
#   watch phase, `owe.next` on the fate of its submission in the report
#   phase, `cut.ph` on an abort. A closing parent admits no submission.
#   An abort of the task submits nothing; the report it owes goes on.
#   The Rust parent's inbox, task runtime and abort marks are this
#   environment; every choice the adversary makes in it is a law's input.

import Base
import ../bend/child.bend as Ch

# Verdicts
# --------

# the watch goes on after verdict x
def watches(x: Ch.Next) -> Bool:
  match x:
    case Ch.Watch{w}:
      True{}
    case Ch.Owe{k}:
      False{}
    case Ch.Quiet{}:
      False{}

# the clock of verdict x is at most full for stall s and fails f
def within(+s: Nat, +f: Nat, x: Ch.Next) -> Bool:
  match x:
    case Ch.Watch{w}:
      match w:
        case Ch.W{t, +l, +n}:
          Bool.and(Nat.is_le(l, s), Nat.is_le(n, f))
    case Ch.Owe{k}:
      True{}
    case Ch.Quiet{}:
      True{}

# call c reports to the parent's inbox
def reports(c: Ch.Call) -> Bool:
  match c:
    case Ch.Watches{w}:
      False{}
    case Ch.Reports{k}:
      True{}
    case Ch.Settles{why}:
      False{}

# Quiet polls
# -----------
# Each takes 1 + dt ms (the Rust watch sleeps a poll interval between
# polls).

type Hush is Data:
  Same{dt: Nat}
  Miss{dt: Nat}

# the token clock w holds
def held(w: Ch.W) -> Maybe<&2, Nat>:
  match w:
    case Ch.W{t, l, n}:
      t

# the shipped verdict on quiet poll h of the watch with clock w: the
# child unsettled with the token w holds, or a failed poll
def Hush.look(+cfg: Ch.Cfg, +w: Ch.W, h: Hush) -> Ch.Next:
  match h:
    case Same{dt}:
      Ch.look(cfg, w, 1n+dt, Ch.Busy{held(w)})
    case Miss{dt}:
      Ch.look(cfg, w, 1n+dt, Ch.Lost{})

# one more quiet poll, if the watch still runs
def hush.step(+cfg: Ch.Cfg, h: Hush, x: Ch.Next) -> Ch.Next:
  match x:
    case Ch.Watch{w}:
      Hush.look(cfg, w, h)
    case Ch.Owe{k}:
      Ch.Owe{k}
    case Ch.Quiet{}:
      Ch.Quiet{}

# the verdict after the quiet polls hs, from verdict x
def hush(hs: List<&2, Hush>, +cfg: Ch.Cfg, x: Ch.Next) -> Ch.Next:
  match hs:
    case Nil{}:
      x
    case h <> t:
      hush(t, cfg, hush.step(cfg, h, x))

# failed polls that took 1 + d ms each
def misses(ds: List<&2, Nat>) -> List<&2, Hush>:
  match ds:
    case Nil{}:
      Nil{}
    case d <> t:
      Miss{d} <> misses(t)

# The parent's inbox
# ------------------

# one submission of the report: its id (1, 2, ...) and fate
type Sub is Data:
  Sub{id: Nat, fate: Ch.Fate}

# What the parent does to its queued submissions: its run places one (m),
# it withdraws one (m), or an abort or a close withdraws them all. A
# settled submission stays as it settled.
type Act is Data:
  Place{m: Nat}
  Pull{m: Nat}
  PullAll{}

def Act.hit(hit: Bool, f: Ch.Fate) -> Ch.Fate:
  match hit:
    case True{}:
      f
    case False{}:
      Ch.Queued{}

# the act on the queued submission with id i
def Act.queued(a: Act, +i: Nat) -> Ch.Fate:
  match a:
    case Place{m}:
      Act.hit(Nat.is_eq(i, m), Ch.Placed{})
    case Pull{m}:
      Act.hit(Nat.is_eq(i, m), Ch.Withdrawn{})
    case PullAll{}:
      Ch.Withdrawn{}

def Fate.act(a: Act, +i: Nat, f: Ch.Fate) -> Ch.Fate:
  match f:
    case Ch.Queued{}:
      Act.queued(a, i)
    case Ch.Withdrawn{}:
      Ch.Withdrawn{}
    case Ch.Placed{}:
      Ch.Placed{}

def act(inbox: List<&2, Sub>, +a: Act) -> List<&2, Sub>:
  match inbox:
    case Nil{}:
      Nil{}
    case s <> rest:
      match s:
        case Sub{+i, f}:
          Sub{i, Fate.act(a, i, f)} <> act(rest, a)

def fate.here(same: Bool, f: Ch.Fate) -> Maybe<&2, Ch.Fate>:
  match same:
    case True{}:
      Some{f}
    case False{}:
      None{}

# the fate of the submission with id n, if the parent has one (the Rust
# harness finds a submission by its request id)
def fate(inbox: List<&2, Sub>, +n: Nat) -> Maybe<&2, Ch.Fate>:
  match inbox:
    case Nil{}:
      None{}
    case s <> rest:
      match s:
        case Sub{+i, f}:
          Maybe.or(&2, Ch.Fate, fate.here(Nat.is_eq(i, n), f), fate(rest, n))

# The task
# --------

# ph: the task's phase; cut: its abort mark (Some{delete}); open: the
# parent is open; inbox: the parent's submissions of the report, newest
# first
type St is Data:
  St{ph: Ch.Ph, cut: Maybe<&2, Bool>, open: Bool, inbox: List<&2, Sub>}

# a task that starts watching its child with clock w: no mark, the parent
# open, nothing submitted
def St.init(w: Ch.W) -> St:
  St{Ch.Watching{w}, None{}, True{}, Nil{}}

def St.ph(s: St) -> Ch.Ph:
  match s:
    case St{ph, c, o, i}:
      ph

def St.inbox(s: St) -> List<&2, Sub>:
  match s:
    case St{ph, c, o, i}:
      i

# the task owes a report
def owing(ph: Ch.Ph) -> Bool:
  match ph:
    case Ch.Watching{w}:
      False{}
    case Ch.Owing{k, n}:
      True{}
    case Ch.Ended{}:
      False{}

# the id the task's report goes under (0 when it owes none)
def St.owed(s: St) -> Nat:
  match s:
    case St{ph, c, o, i}:
      match ph:
        case Ch.Watching{w}:
          0n
        case Ch.Owing{k, n}:
          n
        case Ch.Ended{}:
          0n

# a submission of report k under id n: queued in an open parent's inbox; a
# closing parent admits none (the task waits on it)
def owe.new(open: Bool, k: Ch.Report, +n: Nat, inbox: List<&2, Sub>) -> St:
  match open:
    case True{}:
      St{Ch.Owing{k, n}, None{}, True{}, Sub{n, Ch.Queued{}} <> inbox}
    case False{}:
      St{Ch.Owing{k, n}, None{}, False{}, inbox}

# the Rust report phase carrying out move mv of report k owed under n:
# submit, wait, owe it under the next id (its next invocation submits it),
# or end
def owe.do(mv: Ch.Move, k: Ch.Report, +n: Nat, open: Bool, inbox: List<&2, Sub>) -> St:
  match mv:
    case Ch.Submit{m}:
      owe.new(open, k, m, inbox)
    case Ch.Await{}:
      St{Ch.Owing{k, n}, None{}, open, inbox}
    case Ch.Resubmit{m}:
      St{Ch.Owing{k, m}, None{}, open, inbox}
    case Ch.Delivered{}:
      St{Ch.Ended{}, None{}, open, inbox}

# the Rust watch phase's next phase on the task's call (`watched_next`):
# watch on, owe the report under the first id, or end
def watched(c: Ch.Call) -> Ch.Ph:
  match c:
    case Ch.Watches{w}:
      Ch.Watching{w}
    case Ch.Reports{k}:
      Ch.Owing{k, 1n}
    case Ch.Settles{why}:
      Ch.Ended{}

# the task's step with no abort mark: a poll that reads o dt + 1 ms after
# the last (an inbox task, the shipped `verdict`), or the report phase on
# its submission's fate (the shipped `owe.next`)
def task.run(+cfg: Ch.Cfg, ph: Ch.Ph, open: Bool, +inbox: List<&2, Sub>, +dt: Nat, o: Ch.Obs) -> St:
  match ph:
    case Ch.Watching{+w}:
      St{watched(Ch.verdict(cfg, w, 1n+dt, o, Ch.Inbox{})), None{}, open, inbox}
    case Ch.Owing{k, +n}:
      owe.do(Ch.owe.next(fate(inbox, n), n), k, n, open, inbox)
    case Ch.Ended{}:
      St{Ch.Ended{}, None{}, open, inbox}

# the task's step: an abort mark runs the abort (the shipped `cut.ph`),
# which submits nothing; a closing parent stops only its submissions
def task(+cfg: Ch.Cfg, ph: Ch.Ph, cut: Maybe<&2, Bool>, open: Bool, +inbox: List<&2, Sub>, +dt: Nat, o: Ch.Obs) -> St:
  match cut:
    case None{}:
      task.run(cfg, ph, open, inbox, dt, o)
    case Some{del}:
      St{Ch.cut.ph(ph, del), None{}, open, inbox}

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
  Poll{dt: Nat, o: Ch.Obs}
  Deliver{m: Nat}
  Withdraw{m: Nat}
  Abort{}
  Shut{}
  Reopen{}
  Cut{del: Bool}

def step(+cfg: Ch.Cfg, s: St, e: Ev) -> St:
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

def run(evs: List<&2, Ev>, +cfg: Ch.Cfg, s: St) -> St:
  match evs:
    case Nil{}:
      s
    case e <> t:
      run(t, cfg, step(cfg, s, e))

# What the laws count
# -------------------

def Fate.placed(f: Ch.Fate) -> Nat:
  match f:
    case Ch.Queued{}:
      0n
    case Ch.Withdrawn{}:
      0n
    case Ch.Placed{}:
      1n

def Fate.live(f: Ch.Fate) -> Nat:
  match f:
    case Ch.Queued{}:
      1n
    case Ch.Withdrawn{}:
      0n
    case Ch.Placed{}:
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

# The decisions, spelled for the laws
# -----------------------------------
# What the laws of laws/child.bend require of the shipped decisions, over
# the constructors (never the code's own helpers).

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
