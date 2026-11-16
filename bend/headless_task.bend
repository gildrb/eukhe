# headless_task: whether the exit of a headless run (`eukhe -p`,
# `--mode json`; bend/headless_exit.bend) stands for the run's task. A
# goal is the agent's statement of the task (seeded by `--goal`, or
# created by the agent): it is done only when the agent claimed it
# complete. A run that answered while its goal is still open (active,
# paused, budget-limited, failed) did not finish its task: it is
# incomplete and exits 1, never 0. A run that answered without an open
# goal (none, or one the agent claimed complete) is judged by its final
# answer: an independent judge (one model request without tools) reads
# whether the answer states work left; work left is incomplete (a goal
# claimed complete does not overrule it), an answer the judge could not
# judge exits 1 as unjudged, and an answer that states none (a question
# answered) stands. Every
# other exit stands as headless_exit decided it: a failure keeps its code
# and cause, a budget-limited run stays budget-limited. Entry:
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

# the judge's reading of the final answer: not asked (an open goal
# decides, the run did not answer, or it answered with no text), the answer states
# no work left, it states work left, or the judge gave no verdict (its
# request failed, was stopped, or its reply was unreadable)
type Report is Data:
  RUnasked{}
  RDone{}
  RLeft{}
  RUnjudged{}

# the facts of a finished headless run's task: the cause of its exit
# (bend/headless_exit.bend), its goal, and the judge's reading of its
# final answer
type Facts is Data:
  Facts{cause: Hx.Cause, goal: Goal, report: Report}

# the task: the run's exit stands, the run answered with work left (its
# goal open, or its answer stating work left), or its answer could not be
# judged
type Task is Data:
  Stands{}
  Incomplete{}
  Unjudged{}

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

# the task of an answered run without an open goal: what its final
# answer states
def task.report(r: Report) -> Task:
  match r:
    case RUnasked{}:
      Stands{}
    case RDone{}:
      Stands{}
    case RLeft{}:
      Incomplete{}
    case RUnjudged{}:
      Unjudged{}

# the task of a run without an open goal: its final answer decides when
# it answered
def task.closed(answer: Bool, r: Report) -> Task:
  match answer:
    case True{}:
      task.report(r)
    case False{}:
      Stands{}

# an answered run with an open goal is incomplete; without one (no goal,
# or one claimed complete) its final answer decides
def task(c: Hx.Cause, g: Goal, r: Report) -> Task:
  match g:
    case NoGoal{}:
      task.closed(answered(c), r)
    case Complete{}:
      task.closed(answered(c), r)
    case Open{}:
      task.open(answered(c))

# the code of a task whose run exited with cause c
def verdict(c: Hx.Cause, t: Task) -> Verdict:
  match t:
    case Stands{}:
      Verdict{Hx.code(c), Stands{}}
    case Incomplete{}:
      Verdict{1n, Incomplete{}}
    case Unjudged{}:
      Verdict{1n, Unjudged{}}

# the exit of the task of a finished headless run
def decide(f: Facts) -> Verdict:
  match f:
    case Facts{+c, g, r}:
      verdict(c, task(c, g, r))
