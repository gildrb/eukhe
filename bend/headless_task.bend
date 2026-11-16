# headless_task: whether the exit of a headless run (`eukhe -p`,
# `--mode json`; bend/headless_exit.bend) stands for the run's task. A
# goal is the agent's statement of the task (seeded by `--goal`, or
# created by the agent): it is done only when the agent claimed it
# complete. A run that answered while its goal is still open (active,
# paused, budget-limited, failed) did not finish its task: it is
# incomplete and exits 1, never 0. A run without a goal states no task to
# judge (a question answered), and every other exit stands as
# headless_exit decided it: a failure keeps its code and cause, a
# budget-limited run stays budget-limited. Entry:
# bend/ffi_headless_task.bend (Rust: eukhe-bend rules/headless.rs
# `task`). Laws: laws/headless_task.bend.
#
# Pure: no IO, no @unsafe.

import Base
import ./headless_exit.bend as Hx

# Types
# -----

# the run's goal when the run ends: none, claimed complete, or open
# (active, paused, budget-limited, failed)
type Goal is Data:
  NoGoal{}
  Complete{}
  Open{}

# the facts of a finished headless run's task: the cause of its exit
# (bend/headless_exit.bend) and its goal
type Facts is Data:
  Facts{cause: Hx.Cause, goal: Goal}

# the task: the run's exit stands, or the run answered with its goal open
type Task is Data:
  Stands{}
  Incomplete{}

# the exit of the task: the process code and the task
type Verdict is Data:
  Verdict{code: Nat, task: Task}

# The rule
# --------

# whether the exit is that the run answered
def answered(c: Hx.Cause) -> Bool:
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

# the task of a run whose goal is open: incomplete when it answered
def task.open(answer: Bool) -> Task:
  match answer:
    case True{}:
      Incomplete{}
    case False{}:
      Stands{}

# an answered run with an open goal is incomplete
def task(c: Hx.Cause, g: Goal) -> Task:
  match g:
    case NoGoal{}:
      Stands{}
    case Complete{}:
      Stands{}
    case Open{}:
      task.open(answered(c))

# the code of a task whose run exited with cause c
def verdict(c: Hx.Cause, t: Task) -> Verdict:
  match t:
    case Stands{}:
      Verdict{Hx.code(c), Stands{}}
    case Incomplete{}:
      Verdict{1n, Incomplete{}}

# the exit of the task of a finished headless run
def decide(f: Facts) -> Verdict:
  match f:
    case Facts{+c, g}:
      verdict(c, task(c, g))
