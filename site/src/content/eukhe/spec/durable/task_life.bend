# durable (spec): the lifecycle of a durable task (area task_life) as
# pi-durable states it (spec §5.1-§5.5), restated without the rules of
# bend/task_life.bend:
# the legal transitions (by transition, then by state), the resume map,
# the two join policies, abort marks and the reach of a cascade, a
# measure on states, and the status of a submission
# (types/submissions.rs). spec/durable/task_life_wire.bend holds the wire
# of the entry. The laws of area task_life (laws/task_life.bend) state
# that the rules refine it. A spec: the shipped code never calls it.
#
# S1: a terminal task never changes.
# S2: a reservation runs a pending, running or waiting task at its
#     checkpoint; a held (completing) task runs no code.
# S3: only a running task commits: a checkpoint (running), a wait
#     (waiting, its checkpoint and policy) or an outcome; only a running
#     task is handed back to pending, at its own checkpoint.
# S4: an outcome decided (committed, or written by the scheduler for a
#     live task that is not held) holds as completing while owned work is
#     live, else it is terminal; a held outcome becomes terminal, the same
#     outcome, once no owned work is live.
# S5: resume: a running task becomes pending at its checkpoint; a failFast
#     wait is checked again; nothing else changes.
# S6: a waiting task may run once none of its awaited tasks is live
#     (both policies). allSettled marks nothing. failFast, once an awaited
#     task holds or ended with an outcome other than completed, marks each
#     live awaited task that did not fail.
# S7: marks are ordered none < restart < request; adding a mark keeps the
#     stronger.
# S8: a cascade marks each live foreground task its owner's walk reached,
#     only when the owner is live and has intent (a mark, or a held
#     outcome other than completed), with the owner's reason (restart for
#     an abandoned owner that did not fail, else request), and nothing
#     else.

import Base
import ../../bend/task_life.bend as Tl
import ../../bend/submission.bend as Sb

# The transitions (S1-S4)
# -----------------------

# an outcome decided with owned work live (held) or not
def hold_spec(o: Tl.Outcome, h: Bool) -> Result<&2, &2, Tl.Why, Tl.St>:
  match h:
    case False{}:
      Done{Tl.Terminal{o}}
    case True{}:
      Done{Tl.Completing{o}}

def reserve_spec(s: Tl.St) -> Result<&2, &2, Tl.Why, Tl.St>:
  match s:
    case Tl.Terminal{o}:
      Fail{Tl.Ended{}}
    case Tl.Completing{o}:
      Fail{Tl.Held{}}
    case Tl.Pending{c}:
      Done{Tl.Running{c}}
    case Tl.Running{c}:
      Done{Tl.Running{c}}
    case Tl.Waiting{c, p}:
      Done{Tl.Running{c}}

def committed_spec(n: Tl.Next, h: Bool) -> Result<&2, &2, Tl.Why, Tl.St>:
  match n:
    case Tl.NEnd{o}:
      hold_spec(o, h)
    case Tl.NRun{c}:
      Done{Tl.Running{c}}
    case Tl.NWait{c, p}:
      Done{Tl.Waiting{c, p}}

def commit_spec(s: Tl.St, n: Tl.Next, h: Bool) -> Result<&2, &2, Tl.Why, Tl.St>:
  match s:
    case Tl.Terminal{o}:
      Fail{Tl.Ended{}}
    case Tl.Completing{o}:
      Fail{Tl.Held{}}
    case Tl.Running{c}:
      committed_spec(n, h)
    case Tl.Pending{c}:
      Fail{Tl.NotRunning{}}
    case Tl.Waiting{c, p}:
      Fail{Tl.NotRunning{}}

def requeue_spec(s: Tl.St) -> Result<&2, &2, Tl.Why, Tl.St>:
  match s:
    case Tl.Terminal{o}:
      Fail{Tl.Ended{}}
    case Tl.Completing{o}:
      Fail{Tl.Held{}}
    case Tl.Running{c}:
      Done{Tl.Pending{c}}
    case Tl.Pending{c}:
      Fail{Tl.NotRunning{}}
    case Tl.Waiting{c, p}:
      Fail{Tl.NotRunning{}}

def settle_spec(s: Tl.St, o: Tl.Outcome, h: Bool) -> Result<&2, &2, Tl.Why, Tl.St>:
  match s:
    case Tl.Terminal{q}:
      Fail{Tl.Ended{}}
    case Tl.Completing{q}:
      Fail{Tl.Held{}}
    case Tl.Pending{c}:
      hold_spec(o, h)
    case Tl.Running{c}:
      hold_spec(o, h)
    case Tl.Waiting{c, p}:
      hold_spec(o, h)

def finalize_spec(s: Tl.St, h: Bool) -> Result<&2, &2, Tl.Why, Tl.St>:
  match s:
    case Tl.Terminal{o}:
      Fail{Tl.Ended{}}
    case Tl.Completing{o}:
      hold_spec(o, h)
    case Tl.Pending{c}:
      Fail{Tl.NotHeld{}}
    case Tl.Running{c}:
      Fail{Tl.NotHeld{}}
    case Tl.Waiting{c, p}:
      Fail{Tl.NotHeld{}}

# the state after transition e, by transition first
def step_spec(s: Tl.St, e: Tl.Ev) -> Result<&2, &2, Tl.Why, Tl.St>:
  match e:
    case Tl.Reserve{}:
      reserve_spec(s)
    case Tl.Commit{n, h}:
      commit_spec(s, n, h)
    case Tl.Requeue{}:
      requeue_spec(s)
    case Tl.Settle{o, h}:
      settle_spec(s, o, h)
    case Tl.Finalize{h}:
      finalize_spec(s, h)

# Measures and views
# ------------------

# how far a state is: pending 0, running or waiting 1, completing 2,
# terminal 3
def rank(s: Tl.St) -> Nat:
  match s:
    case Tl.Pending{c}:
      0n
    case Tl.Running{c}:
      1n
    case Tl.Waiting{c, p}:
      1n
    case Tl.Completing{o}:
      2n
    case Tl.Terminal{o}:
      3n

# t goes back from s only as a running task put back to pending at its
# own checkpoint
def back_ok.to(c: Nat, t: Tl.St) -> Bool:
  match t:
    case Tl.Pending{d}:
      Nat.is_eq(c, d)
    case Tl.Running{d}:
      False{}
    case Tl.Waiting{d, p}:
      False{}
    case Tl.Completing{o}:
      False{}
    case Tl.Terminal{o}:
      False{}

def back_ok(s: Tl.St, t: Tl.St) -> Bool:
  match s:
    case Tl.Running{c}:
      back_ok.to(c, t)
    case Tl.Pending{c}:
      False{}
    case Tl.Waiting{c, p}:
      False{}
    case Tl.Completing{o}:
      False{}
    case Tl.Terminal{o}:
      False{}

# a transition from s never lowers the measure, but for back_ok
def forward_ok(+s: Tl.St, r: Result<&2, &2, Tl.Why, Tl.St>) -> Bool:
  match r:
    case Fail{y}:
      True{}
    case Done{+t}:
      Bool.or(Nat.is_le(rank(s), rank(t)), back_ok(s, t))

# the checkpoint of a live state
def st_cp(s: Tl.St) -> Maybe<&2, Nat>:
  match s:
    case Tl.Pending{c}:
      Some{c}
    case Tl.Running{c}:
      Some{c}
    case Tl.Waiting{c, p}:
      Some{c}
    case Tl.Completing{o}:
      None{}
    case Tl.Terminal{o}:
      None{}

# the outcome of a completing or terminal state
def st_out(s: Tl.St) -> Maybe<&2, Tl.Outcome>:
  match s:
    case Tl.Pending{c}:
      None{}
    case Tl.Running{c}:
      None{}
    case Tl.Waiting{c, p}:
      None{}
    case Tl.Completing{o}:
      Some{o}
    case Tl.Terminal{o}:
      Some{o}

def is_running(s: Tl.St) -> Bool:
  match s:
    case Tl.Pending{c}:
      False{}
    case Tl.Running{c}:
      True{}
    case Tl.Waiting{c, p}:
      False{}
    case Tl.Completing{o}:
      False{}
    case Tl.Terminal{o}:
      False{}

# the outcome after a transition from a task holding o: o when refused
def outcome_after(r: Result<&2, &2, Tl.Why, Tl.St>, o: Tl.Outcome) -> Maybe<&2, Tl.Outcome>:
  match r:
    case Fail{y}:
      Some{o}
    case Done{t}:
      st_out(t)

# Resume (S5)
# -----------

def resume_spec(s: Tl.St) -> Tl.St & Bool:
  match s:
    case Tl.Running{c}:
      (Tl.Pending{c}, False{})
    case Tl.Waiting{c, p}:
      match p:
        case Tl.FailFast{}:
          (Tl.Waiting{c, Tl.FailFast{}}, True{})
        case Tl.AllSettled{}:
          (Tl.Waiting{c, Tl.AllSettled{}}, False{})
    case Tl.Pending{c}:
      (Tl.Pending{c}, False{})
    case Tl.Completing{o}:
      (Tl.Completing{o}, False{})
    case Tl.Terminal{o}:
      (Tl.Terminal{o}, False{})

def resumed(r: Tl.St & Bool) -> Tl.St:
  (s, b) = r
  s

# Join (S6)
# ---------

# some item is True
def some(xs: List<&2, Bool>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> t:
      Bool.or(x, some(t))

# the i-th failure flag, False past the end
def flag_at(fs: List<&2, Bool>) -> Bool:
  match fs:
    case Nil{}:
      False{}
    case f <> t:
      f

def flags_tail(fs: List<&2, Bool>) -> List<&2, Bool>:
  match fs:
    case Nil{}:
      Nil{}
    case f <> t:
      t

# failFast: with a failure somewhere (hit), each live awaited task that did
# not fail is marked
def ff_marks(live: List<&2, Bool>, +fs: List<&2, Bool>, +hit: Bool) -> List<&2, Bool>:
  match live:
    case Nil{}:
      Nil{}
    case l <> t:
      Bool.and(hit, Bool.and(l, Bool.not(flag_at(fs)))) <> ff_marks(t, flags_tail(fs), hit)

def none_marked(live: List<&2, Bool>) -> List<&2, Bool>:
  match live:
    case Nil{}:
      Nil{}
    case l <> t:
      False{} <> none_marked(t)

def join_ff_spec(+live: List<&2, Bool>, +fs: List<&2, Bool>) -> Bool & List<&2, Bool>:
  (Bool.not(some(live)), ff_marks(live, fs, some(fs)))

def join_as_spec(+live: List<&2, Bool>, fs: List<&2, Bool>) -> Bool & List<&2, Bool>:
  (Bool.not(some(live)), none_marked(live))

# Marks and cascades (S7, S8)
# ---------------------------

def mark_rank(m: Tl.Mark) -> Nat:
  match m:
    case Tl.Clear{}:
      0n
    case Tl.Restart{}:
      1n
    case Tl.Request{}:
      2n

def pick_mark(b: Bool, x: Tl.Mark, y: Tl.Mark) -> Tl.Mark:
  match b:
    case True{}:
      x
    case False{}:
      y

# the stronger of two marks
def merge_spec(+a: Tl.Mark, +b: Tl.Mark) -> Tl.Mark:
  pick_mark(Nat.is_lt(mark_rank(a), mark_rank(b)), b, a)

def res_ok(r: Tl.Res) -> Bool:
  match r:
    case Tl.RCompleted{}:
      True{}
    case Tl.RFailed{}:
      False{}
    case Tl.RAborted{}:
      False{}
    case Tl.ROrphaned{}:
      False{}
    case Tl.RFaulted{}:
      False{}

# s holds or ended with an outcome other than completed
def bad_end(s: Tl.St) -> Bool:
  match s:
    case Tl.Completing{o}:
      match o:
        case Tl.Outcome{r, h}:
          Bool.not(res_ok(r))
    case Tl.Terminal{o}:
      match o:
        case Tl.Outcome{r, h}:
          Bool.not(res_ok(r))
    case Tl.Pending{c}:
      False{}
    case Tl.Running{c}:
      False{}
    case Tl.Waiting{c, p}:
      False{}

def is_terminal(s: Tl.St) -> Bool:
  match s:
    case Tl.Terminal{o}:
      True{}
    case Tl.Pending{c}:
      False{}
    case Tl.Running{c}:
      False{}
    case Tl.Waiting{c, p}:
      False{}
    case Tl.Completing{o}:
      False{}

# an owner cascades: live, with a mark or a held outcome other than
# completed
def intent_spec(+s: Tl.St, m: Tl.Mark) -> Bool:
  Bool.and(Bool.not(is_terminal(s)), Bool.or(Nat.is_lt(0n, mark_rank(m)), bad_end(s)))

# what an owner passes on: restart only from an owner with the restart mark
# that did not fail
def reason_spec(+s: Tl.St, m: Tl.Mark) -> Tl.Mark:
  pick_mark(Bool.and(Nat.is_eq(mark_rank(m), 1n), Bool.not(bad_end(s))), Tl.Restart{}, Tl.Request{})

# one reached task: live and not background, below an owner that cascades
def cascade_row_spec(+go: Bool, +by: Tl.Mark, r: Tl.Row) -> Tl.Mark:
  match r:
    case Tl.Row{l, b, +m}:
      pick_mark(Bool.and(go, Bool.and(l, Bool.not(b))), merge_spec(m, by), m)

def cascade_rows_spec(+go: Bool, +by: Tl.Mark, rs: List<&2, Tl.Row>) -> List<&2, Tl.Mark>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> t:
      cascade_row_spec(go, by, r) <> cascade_rows_spec(go, by, t)

def cascade_spec(+s: Tl.St, +m: Tl.Mark, rs: List<&2, Tl.Row>) -> List<&2, Tl.Mark>:
  cascade_rows_spec(intent_spec(s, m), reason_spec(s, m), rs)

# Submissions
# -----------

# a submission's status (types/submissions.rs SubmissionStatus)
type SubStatus is Data:
  SQueued{}
  SPlaced{}
  SDone{}
  SUnanswered{}

def sub_status(s: Sb.Sub) -> SubStatus:
  match s:
    case Sb.InQueued{}:
      SQueued{}
    case Sb.InPlaced{e}:
      SPlaced{}
    case Sb.InAnswered{e, a}:
      SDone{}
    case Sb.InDropped{m}:
      SUnanswered{}
    case Sb.WrQueued{}:
      SQueued{}
    case Sb.WrPlaced{e}:
      SDone{}
    case Sb.WrDropped{}:
      SUnanswered{}

# queued 0, placed 1, done or unanswered 2
def status_rank(x: SubStatus) -> Nat:
  match x:
    case SQueued{}:
      0n
    case SPlaced{}:
      1n
    case SDone{}:
      2n
    case SUnanswered{}:
      2n

# a change of s moves its status strictly forward, or leaves it
def sub_forward(+s: Sb.Sub, o: Sb.Out) -> Bool:
  match o:
    case Sb.Stays{}:
      True{}
    case Sb.Refused{y}:
      True{}
    case Sb.Moves{n}:
      Nat.is_lt(status_rank(sub_status(s)), status_rank(sub_status(n)))
