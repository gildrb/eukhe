# task_life: the lifecycle of a durable task (port of pi-durable's task
# scheduler, spec §5.1-§5.5; the Rust host is crates/eukhe-durable/src/
# harness/scheduler/). A task is pending, running or waiting (live, with
# the checkpoint it resumes from), completing (its outcome is decided and
# held while ordinary owned work below it is live; it runs no more code)
# or terminal (settled for good). The host keeps every payload (checkpoint
# JSON, the result or error of an outcome) and names each one by a handle:
# a Nat these rules carry but never read.
#
# step: one transition the scheduler writes on the Session line: a
# reservation, a commit of a running task, a handover back to pending, an
# outcome the scheduler decides, the finalization of a held outcome.
# resume: what a new Harness does to a stored state before it schedules.
# join: how a waiting task treats the tasks it waits on (failFast,
# allSettled). merge and cascade: abort marks and how an owner's
# cancellation reaches the live tasks below it.
# Pure: no IO, no @unsafe. laws/task_life.bend states the laws.

import Base

# Types
# -----

# how a waiting task treats the tasks it waits on
type Policy is Data:
  FailFast{}
  AllSettled{}

# how an outcome ended a task (TaskOutcomeStatus)
type Res is Data:
  RCompleted{}
  RFailed{}
  RAborted{}
  ROrphaned{}
  RFaulted{}

# an outcome: how it ended, and the handle of its payload
type Outcome is Data:
  Outcome{res: Res, h: Nat}

# a task state; cp is the handle of a checkpoint
type St is Data:
  Pending{cp: Nat}
  Running{cp: Nat}
  Waiting{cp: Nat, policy: Policy}
  Completing{out: Outcome}
  Terminal{out: Outcome}

# the state a running task commits
type Next is Data:
  NRun{cp: Nat}
  NWait{cp: Nat, policy: Policy}
  NEnd{out: Outcome}

# a transition the scheduler writes; holds: ordinary owned work below the
# task is live
type Ev is Data:
  Reserve{}
  Commit{next: Next, holds: Bool}
  Requeue{}
  Settle{out: Outcome, holds: Bool}
  Finalize{holds: Bool}

# why a transition does not apply
type Why is Data:
  Ended{}
  Held{}
  NotRunning{}
  NotHeld{}

# an abort mark: none, the `restart` mark of an abandoned task, a request
type Mark is Data:
  Clear{}
  Restart{}
  Request{}

# one task a cascade's walk reached below its owner
type Row is Data:
  Row{live: Bool, background: Bool, mark: Mark}

# The step
# --------

# an outcome decided: held while owned work is live, else terminal
def decided(o: Outcome, holds: Bool) -> Result<&2, &2, Why, St>:
  match holds:
    case True{}:
      Done{Completing{o}}
    case False{}:
      Done{Terminal{o}}

# what a running task commits
def commit(n: Next, holds: Bool) -> Result<&2, &2, Why, St>:
  match n:
    case NRun{c}:
      Done{Running{c}}
    case NWait{c, p}:
      Done{Waiting{c, p}}
    case NEnd{o}:
      decided(o, holds)

# a live task with checkpoint c (running: r is True)
def step.live(e: Ev, c: Nat, r: Bool) -> Result<&2, &2, Why, St>:
  match e:
    case Reserve{}:
      Done{Running{c}}
    case Commit{n, h}:
      match r:
        case True{}:
          commit(n, h)
        case False{}:
          Fail{NotRunning{}}
    case Requeue{}:
      match r:
        case True{}:
          Done{Pending{c}}
        case False{}:
          Fail{NotRunning{}}
    case Settle{o, h}:
      decided(o, h)
    case Finalize{h}:
      Fail{NotHeld{}}

# a waiting task with checkpoint c and policy p
def step.waiting(e: Ev, c: Nat, -p: Policy) -> Result<&2, &2, Why, St>:
  match e:
    case Reserve{}:
      Done{Running{c}}
    case Commit{n, h}:
      Fail{NotRunning{}}
    case Requeue{}:
      Fail{NotRunning{}}
    case Settle{o, h}:
      decided(o, h)
    case Finalize{h}:
      Fail{NotHeld{}}

# a completing task holding o
def step.held(e: Ev, o: Outcome) -> Result<&2, &2, Why, St>:
  match e:
    case Reserve{}:
      Fail{Held{}}
    case Commit{n, h}:
      Fail{Held{}}
    case Requeue{}:
      Fail{Held{}}
    case Settle{q, h}:
      Fail{Held{}}
    case Finalize{h}:
      decided(o, h)

# the state after transition e, or why it does not apply
def step(s: St, e: Ev) -> Result<&2, &2, Why, St>:
  match s:
    case Pending{c}:
      step.live(e, c, False{})
    case Running{c}:
      step.live(e, c, True{})
    case Waiting{c, p}:
      step.waiting(e, c, p)
    case Completing{o}:
      step.held(e, o)
    case Terminal{o}:
      Fail{Ended{}}

# Resume
# ------

def fail_fast(p: Policy) -> Bool:
  match p:
    case FailFast{}:
      True{}
    case AllSettled{}:
      False{}

# a stored state when a new Harness opens: a running task is pending at
# its checkpoint (no invocation survives); the rest stays. The Bool: a
# failFast wait to check again.
def resume(s: St) -> St & Bool:
  match s:
    case Pending{c}:
      (Pending{c}, False{})
    case Running{c}:
      (Pending{c}, False{})
    case Waiting{c, +p}:
      (Waiting{c, p}, fail_fast(p))
    case Completing{o}:
      (Completing{o}, False{})
    case Terminal{o}:
      (Terminal{o}, False{})

# Join
# ----

def any(xs: List<&2, Bool>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> t:
      match x:
        case True{}:
          True{}
        case False{}:
          any(t)

# no mark for each awaited task
def keep_all(xs: List<&2, Bool>) -> List<&2, Bool>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      False{} <> keep_all(t)

# a mark for each live awaited task that did not fail
def abort_others(live: List<&2, Bool>, failed: List<&2, Bool>) -> List<&2, Bool>:
  match live:
    case Nil{}:
      Nil{}
    case l <> t:
      match failed:
        case Nil{}:
          l <> abort_others(t, Nil{})
        case f <> u:
          Bool.and(l, Bool.not(f)) <> abort_others(t, u)

def join.marks(p: Policy, hit: Bool, +live: List<&2, Bool>, failed: List<&2, Bool>) -> List<&2, Bool>:
  match p:
    case FailFast{}:
      match hit:
        case True{}:
          abort_others(live, failed)
        case False{}:
          keep_all(live)
    case AllSettled{}:
      keep_all(live)

# a waiting task over its awaited tasks (each live or not, each holding or
# ended with an outcome other than completed or not): whether it may run
# (no awaited task is live), and the awaited tasks to abort
def join(p: Policy, +live: List<&2, Bool>, +failed: List<&2, Bool>) -> Bool & List<&2, Bool>:
  (Bool.not(any(live)), join.marks(p, any(failed), live, failed))

# Abort marks
# -----------

# the stronger of two marks: a request over a `restart` mark over none
def merge(a: Mark, b: Mark) -> Mark:
  match a:
    case Clear{}:
      b
    case Restart{}:
      match b:
        case Clear{}:
          Restart{}
        case Restart{}:
          Restart{}
        case Request{}:
          Request{}
    case Request{}:
      Request{}

# an outcome other than completed
def res_failed(r: Res) -> Bool:
  match r:
    case RCompleted{}:
      False{}
    case RFailed{}:
      True{}
    case RAborted{}:
      True{}
    case ROrphaned{}:
      True{}
    case RFaulted{}:
      True{}

def out_failed(o: Outcome) -> Bool:
  match o:
    case Outcome{r, h}:
      res_failed(r)

# s holds or ended with an outcome other than completed
def failed(s: St) -> Bool:
  match s:
    case Pending{c}:
      False{}
    case Running{c}:
      False{}
    case Waiting{c, p}:
      False{}
    case Completing{o}:
      out_failed(o)
    case Terminal{o}:
      out_failed(o)

# s is live: not terminal
def live(s: St) -> Bool:
  match s:
    case Pending{c}:
      True{}
    case Running{c}:
      True{}
    case Waiting{c, p}:
      True{}
    case Completing{o}:
      True{}
    case Terminal{o}:
      False{}

def marked(m: Mark) -> Bool:
  match m:
    case Clear{}:
      False{}
    case Restart{}:
      True{}
    case Request{}:
      True{}

# a live owner's cancellation intent: its abort mark, or a held outcome
# other than completed (a terminal owner never cascades)
def intent(+s: St, m: Mark) -> Bool:
  Bool.and(live(s), Bool.or(marked(m), failed(s)))

# the mark an owner passes on: an owner abandoned after a restart passes
# its `restart` mark, unless it holds a failed outcome; anything else is a
# request
def reason.restart(f: Bool) -> Mark:
  match f:
    case True{}:
      Request{}
    case False{}:
      Restart{}

def reason(+s: St, m: Mark) -> Mark:
  match m:
    case Clear{}:
      Request{}
    case Restart{}:
      reason.restart(failed(s))
    case Request{}:
      Request{}

def cascade.pick(hit: Bool, m: Mark, by: Mark) -> Mark:
  match hit:
    case True{}:
      merge(m, by)
    case False{}:
      m

def cascade.row(go: Bool, +by: Mark, r: Row) -> Mark:
  match r:
    case Row{l, b, m}:
      cascade.pick(Bool.and(go, Bool.and(l, Bool.not(b))), m, by)

def cascade.rows(+go: Bool, +by: Mark, rs: List<&2, Row>) -> List<&2, Mark>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> t:
      cascade.row(go, by, r) <> cascade.rows(go, by, t)

# an owner in state s with mark m over the tasks its walk reached: the
# mark each one has after the cascade (a live foreground task below an
# owner with intent takes the owner's reason; anything else keeps its
# mark)
def cascade(+s: St, +m: Mark, rs: List<&2, Row>) -> List<&2, Mark>:
  cascade.rows(intent(s, m), reason(s, m), rs)
