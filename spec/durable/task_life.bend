# durable (spec): the lifecycle of a durable task (area task_life) as
# the durable task spec states it (§5.1-§5.5): the terms the laws of area
# task_life (laws/task_life.bend) state the rules of bend/task_life.bend
# with. They name what a state, a list or a mark holds (a checkpoint, an
# outcome, the i-th flag, a count, the rank of a mark); none of them
# decides a transition, a resume, a join or a cascade. A measure on
# states, and the status of a submission (types/submissions.rs).
# spec/durable/task_life_wire.bend holds the wire of the entry. A spec:
# the shipped code never calls it.
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

# the outcome after a transition from a task holding o: o when refused
def outcome_after(r: Result<&2, &2, Tl.Why, Tl.St>, o: Tl.Outcome) -> Maybe<&2, Tl.Outcome>:
  match r:
    case Fail{y}:
      Some{o}
    case Done{t}:
      st_out(t)

# Resume (S5)
# -----------

# the state a resume leaves
def resumed(r: Tl.St & Bool) -> Tl.St:
  (s, b) = r
  s

# whether a resume asks for the failFast check
def recheck(r: Tl.St & Bool) -> Bool:
  (s, b) = r
  b

# Join (S6)
# ---------

# whether the waiting task may run
def may_run(r: Bool & List<&2, Bool>) -> Bool:
  (ok, ms) = r
  ok

# the abort marks of a join, one per awaited task
def marks(r: Bool & List<&2, Bool>) -> List<&2, Bool>:
  (ok, ms) = r
  ms

# how many flags of xs are set
def count(xs: List<&2, Bool>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case x <> t:
      match x:
        case True{}:
          1n+count(t)
        case False{}:
          count(t)

# the i-th flag of xs (from 0); unset past the end
def at(xs: List<&2, Bool>, i: Nat) -> Bool:
  match xs i:
    case Nil{} _:
      False{}
    case x <> t 0n:
      x
    case x <> t 1n+p:
      at(t, p)

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

# an outcome that completed
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

# s holds or ended with an outcome other than completed (S8: it failed)
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

# the mark of each reached task, in order
def own_marks(rs: List<&2, Tl.Row>) -> List<&2, Tl.Mark>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> t:
      match r:
        case Tl.Row{l, b, m}:
          m <> own_marks(t)

# the mark of a reached task, if there is one
def row_mark(r: Maybe<&2, Tl.Row>) -> Maybe<&2, Tl.Mark>:
  match r:
    case None{}:
      None{}
    case Some{x}:
      match x:
        case Tl.Row{l, b, m}:
          Some{m}

# the reached task is live and runs in the foreground
def row_hit(r: Tl.Row) -> Bool:
  match r:
    case Tl.Row{l, b, m}:
      Bool.and(l, Bool.not(b))

# reached task i (from 0) exists, is live and runs in the foreground
def hit_at(rs: List<&2, Tl.Row>, i: Nat) -> Bool:
  match rs i:
    case Nil{} _:
      False{}
    case r <> t 0n:
      row_hit(r)
    case r <> t 1n+p:
      hit_at(t, p)

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
