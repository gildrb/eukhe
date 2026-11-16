# durable (spec): whether the exit of a headless run (`eukhe -p`,
# `--mode json`) stands for its task, stated without the rule of
# bend/headless_task.bend, and the wire of its entry
# (bend/ffi_headless_task.bend, crates/eukhe-bend/WIRE.md). The laws of
# area headless_task state T1-T3 and W6-W8 one property at a time, with
# the helpers below. A spec: the shipped code never calls it.
#
# T1: a goal is the agent's statement of the run's task (seeded by
#     `--goal` or created by the agent); it is done only when the agent
#     claimed it complete. A goal still active, paused, budget-limited or
#     failed when the run ends is open.
# T2: a run whose exit says it answered (headless_exit E1) while its goal
#     is open is incomplete: it exits 1. It never exits 0.
# T3: every other exit stands as headless_exit decided it, code and
#     cause: a run without a goal (a question answered), a run whose goal
#     is complete, every failure, a budget-limited run.
# W6: a request is the exit's cause, spelled as the headless_exit entry
#     replies it (W4), then the goal: 0 none | 1 complete | 2 open.
# W7: a reply is the code (Nat), then the task: 0 the exit stands |
#     1 incomplete.
# W8: anything else is no request.

import Base
import ../../bend/headless_exit.bend as Hx
import ../../bend/headless_task.bend as Ht
import ../../bend/wire.bend as Wr
import ./headless_wire.bend as SpW

# The task (T1-T3)
# ----------------

# T1: the goal is open
def goal_open(g: Ht.Goal) -> Bool:
  match g:
    case Ht.NoGoal{}:
      False{}
    case Ht.Complete{}:
      False{}
    case Ht.Open{}:
      True{}

# T2: the exit says the run answered
def exit_answered(c: Hx.Cause) -> Bool:
  match c:
    case Hx.CAnswered{}:
      True{}
    case Hx.CCommandFailed{}:
      False{}
    case Hx.CGaveUp{}:
      False{}
    case Hx.CRunFailed{r}:
      False{}
    case Hx.CProviderError{}:
      False{}
    case Hx.CAborted{}:
      False{}
    case Hx.CUnfinished{}:
      False{}
    case Hx.CSlashFailed{}:
      False{}
    case Hx.CCompactionFailed{}:
      False{}
    case Hx.CAutonomousFailed{}:
      False{}
    case Hx.CBudgetLimited{}:
      False{}
    case Hx.CBudgetUnanswered{}:
      False{}

# T2: the run answered with its goal open
def unfinished(f: Ht.Facts) -> Bool:
  match f:
    case Ht.Facts{c, g}:
      Bool.and(exit_answered(c), goal_open(g))

# the cause of the run's exit
def cause_of(f: Ht.Facts) -> Hx.Cause:
  match f:
    case Ht.Facts{c, g}:
      c

# whether a task's exit is incomplete
def incomplete(v: Ht.Verdict) -> Bool:
  match v:
    case Ht.Verdict{n, t}:
      match t:
        case Ht.Stands{}:
          False{}
        case Ht.Incomplete{}:
          True{}

# the code of a task's exit
def code_of(v: Ht.Verdict) -> Nat:
  match v:
    case Ht.Verdict{n, t}:
      n

# Requests and replies (W6-W7)
# ----------------------------

def w_goal(g: Ht.Goal, rest: String) -> String:
  match g:
    case Ht.NoGoal{}:
      Wr.put_nat(0n, rest)
    case Ht.Complete{}:
      Wr.put_nat(1n, rest)
    case Ht.Open{}:
      Wr.put_nat(2n, rest)

# a request, then rest
def w_task_req(f: Ht.Facts, rest: String) -> String:
  match f:
    case Ht.Facts{c, g}:
      SpW.w_cause(c, w_goal(g, rest))

def w_task(t: Ht.Task, rest: String) -> String:
  match t:
    case Ht.Stands{}:
      Wr.put_nat(0n, rest)
    case Ht.Incomplete{}:
      Wr.put_nat(1n, rest)

def w_verdict(v: Ht.Verdict, rest: String) -> String:
  match v:
    case Ht.Verdict{n, t}:
      Wr.put_nat(n, w_task(t, rest))

# The reader (W8)
# ---------------

def r_cause.failed(d: Wr.Dec<Hx.Reason>) -> Wr.Dec<Hx.Cause>:
  match d:
    case Wr.Got{r, s}:
      Wr.Got{Hx.CRunFailed{r}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def r_cause(d: Wr.Dec<Nat>) -> Wr.Dec<Hx.Cause>:
  match d:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          Wr.Got{Hx.CAnswered{}, s}
        case 1n:
          Wr.Got{Hx.CCommandFailed{}, s}
        case 2n:
          Wr.Got{Hx.CGaveUp{}, s}
        case 3n:
          r_cause.failed(SpW.r_reason(Wr.get_nat(s)))
        case 4n:
          Wr.Got{Hx.CProviderError{}, s}
        case 5n:
          Wr.Got{Hx.CAborted{}, s}
        case 6n:
          Wr.Got{Hx.CUnfinished{}, s}
        case 7n:
          Wr.Got{Hx.CSlashFailed{}, s}
        case 8n:
          Wr.Got{Hx.CCompactionFailed{}, s}
        case 9n:
          Wr.Got{Hx.CAutonomousFailed{}, s}
        case 10n:
          Wr.Got{Hx.CBudgetLimited{}, s}
        case 11n:
          Wr.Got{Hx.CBudgetUnanswered{}, s}
        case 12n+u:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

def r_goal(d: Wr.Dec<Nat>) -> Wr.Dec<Ht.Goal>:
  match d:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          Wr.Got{Ht.NoGoal{}, s}
        case 1n:
          Wr.Got{Ht.Complete{}, s}
        case 2n:
          Wr.Got{Ht.Open{}, s}
        case 3n+u:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

def r_task.goal(c: Hx.Cause, d: Wr.Dec<Ht.Goal>) -> Wr.Dec<Ht.Facts>:
  match d:
    case Wr.Got{g, s}:
      Wr.Got{Ht.Facts{c, g}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def r_task.cause(d: Wr.Dec<Hx.Cause>) -> Wr.Dec<Ht.Facts>:
  match d:
    case Wr.Got{c, s}:
      r_task.goal(c, r_goal(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

# a request at the start of s, read with the wire's decoders
def r_task(s: String) -> Wr.Dec<Ht.Facts>:
  r_task.cause(r_cause(Wr.get_nat(s)))

def r_task_whole.end(e: Bool, f: Ht.Facts) -> Maybe<&2, Ht.Facts>:
  match e:
    case True{}:
      Some{f}
    case False{}:
      None{}

def r_task_whole(d: Wr.Dec<Ht.Facts>) -> Maybe<&2, Ht.Facts>:
  match d:
    case Wr.Got{f, +s}:
      r_task_whole.end(Wr.end(s), f)
    case Wr.Bad{}:
      None{}

# the request s spells whole, with nothing after it
def read_task(s: String) -> Maybe<&2, Ht.Facts>:
  r_task_whole(r_task(s))
