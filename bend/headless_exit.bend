# headless_exit: the process exit code of a headless run (`eukhe -p`,
# `--mode json`) and its cause. A run that did not answer, or answered
# with a failure, exits nonzero, so a script or CI job never reads a
# failed run as done. Entry: bend/ffi_headless_exit.bend (Rust: eukhe-bend
# rules/headless.rs `exit`). Laws: laws/headless_exit.bend.
#
# The cause is the first failure that holds, in this order: a session
# command prompt failed; the settle wait gave up at its limit, or ended at
# the time budget's deadline; the last run settled unanswered for a
# failure (a model error, the run limit, no model, a forced tool, a fault,
# an abort, a budget refusal, another reason; a reset, a stale run and a
# withdrawn input are no failure of the run); the terminal transcript
# entry is a provider error, a budget refusal, an aborted reply, an
# unfinished reply (a tool use, a pending or deferred turn) or a failed
# slash command; a compaction failed; an autonomous turn failed. With
# none, the run answered.
#
# Budget-limited: when the agent's final answer from the budget's reserve
# was delivered (budget_answered), the facts a used-up budget leaves (the
# wait ended at the deadline, a run or terminal entry the budget refused)
# are no failure, and a run with no other failure is budget-limited.
# Without that answer each of them is a failure: the budget ended the run
# unanswered. The code is 0 for an answered or budget-limited run, else 1.
#
# Pure: no IO, no @unsafe.

import Base

# Types
# -----

# how the settle wait ended: quiet, given up at its limit, or at the time
# budget's deadline
type Wait is Data:
  Quiet{}
  GaveUp{}
  BudgetDeadline{}

# why a run settled unanswered
type Reason is Data:
  ModelError{}
  RunLimit{}
  NoModel{}
  ForcedTool{}
  Faulted{}
  Aborted{}
  Reset{}
  Stale{}
  Withdrawn{}
  Other{}
  BudgetRefused{}

# how the last run settled
type Run is Data:
  NoRun{}
  Answered{}
  Unanswered{reason: Reason}

# the terminal transcript entry: none, an assistant reply that stopped
# (stop, length), one left unfinished (tool use, pending, deferred), a
# provider error, an aborted reply, a slash command that succeeded or
# failed, a request the budget refused
type Primary is Data:
  PNothing{}
  PAnswer{}
  PUnfinished{}
  PProviderError{}
  PAborted{}
  PSlashOk{}
  PSlashFailed{}
  PBudgetRefused{}

# the facts of a finished headless run; budget_answered: the agent's
# budget phase is wrap-up or exhausted and its last reply is its final
# answer from the reserve, delivered
type Facts is Data:
  Facts{command_failed: Bool, wait: Wait, run: Run, primary: Primary, compaction_failed: Bool, autonomous_failed: Bool, budget_answered: Bool}

# why the run exits as it does
type Cause is Data:
  CAnswered{}
  CCommandFailed{}
  CGaveUp{}
  CRunFailed{reason: Reason}
  CProviderError{}
  CAborted{}
  CUnfinished{}
  CSlashFailed{}
  CCompactionFailed{}
  CAutonomousFailed{}
  CBudgetLimited{}
  CBudgetUnanswered{}

# the exit: the process code and its cause
type Verdict is Data:
  Verdict{code: Nat, cause: Cause}

# The rule
# --------

# the code of a cause: 0 for an answered or budget-limited run, 1 for
# every failure
def code(c: Cause) -> Nat:
  match c:
    case CAnswered{}:
      0n
    case CCommandFailed{}:
      1n
    case CGaveUp{}:
      1n
    case CRunFailed{r}:
      1n
    case CProviderError{}:
      1n
    case CAborted{}:
      1n
    case CUnfinished{}:
      1n
    case CSlashFailed{}:
      1n
    case CCompactionFailed{}:
      1n
    case CAutonomousFailed{}:
      1n
    case CBudgetLimited{}:
      0n
    case CBudgetUnanswered{}:
      1n

# the exit of a cause
def verdict(+c: Cause) -> Verdict:
  Verdict{code(c), c}

# a fact a used-up budget leaves: no failure (read on to next) when the
# final answer was delivered, else the run ended unanswered on the budget
def excuse(budget_answered: Bool, next: Cause) -> Cause:
  match budget_answered:
    case True{}:
      next
    case False{}:
      CBudgetUnanswered{}

# after the transcript: a failed compaction, then a failed autonomous
# turn; with neither, budget-limited when the final answer was delivered,
# else answered
def by_flags(compaction_failed: Bool, autonomous_failed: Bool, budget_answered: Bool) -> Cause:
  match compaction_failed:
    case True{}:
      CCompactionFailed{}
    case False{}:
      match autonomous_failed:
        case True{}:
          CAutonomousFailed{}
        case False{}:
          match budget_answered:
            case True{}:
              CBudgetLimited{}
            case False{}:
              CAnswered{}

# after the run: the terminal transcript entry
def by_primary(p: Primary, compaction_failed: Bool, autonomous_failed: Bool, +budget_answered: Bool) -> Cause:
  match p:
    case PNothing{}:
      by_flags(compaction_failed, autonomous_failed, budget_answered)
    case PAnswer{}:
      by_flags(compaction_failed, autonomous_failed, budget_answered)
    case PUnfinished{}:
      CUnfinished{}
    case PProviderError{}:
      CProviderError{}
    case PAborted{}:
      CAborted{}
    case PSlashOk{}:
      by_flags(compaction_failed, autonomous_failed, budget_answered)
    case PSlashFailed{}:
      CSlashFailed{}
    case PBudgetRefused{}:
      excuse(budget_answered, by_flags(compaction_failed, autonomous_failed, budget_answered))

# an unanswered run: its reason, unless the reason is no failure of the run
def by_reason(r: Reason, p: Primary, compaction_failed: Bool, autonomous_failed: Bool, +budget_answered: Bool) -> Cause:
  match r:
    case ModelError{}:
      CRunFailed{ModelError{}}
    case RunLimit{}:
      CRunFailed{RunLimit{}}
    case NoModel{}:
      CRunFailed{NoModel{}}
    case ForcedTool{}:
      CRunFailed{ForcedTool{}}
    case Faulted{}:
      CRunFailed{Faulted{}}
    case Aborted{}:
      CRunFailed{Aborted{}}
    case Reset{}:
      by_primary(p, compaction_failed, autonomous_failed, budget_answered)
    case Stale{}:
      by_primary(p, compaction_failed, autonomous_failed, budget_answered)
    case Withdrawn{}:
      by_primary(p, compaction_failed, autonomous_failed, budget_answered)
    case Other{}:
      CRunFailed{Other{}}
    case BudgetRefused{}:
      excuse(budget_answered, by_primary(p, compaction_failed, autonomous_failed, budget_answered))

# after the wait: the last run's settlement
def by_run(run: Run, p: Primary, compaction_failed: Bool, autonomous_failed: Bool, budget_answered: Bool) -> Cause:
  match run:
    case NoRun{}:
      by_primary(p, compaction_failed, autonomous_failed, budget_answered)
    case Answered{}:
      by_primary(p, compaction_failed, autonomous_failed, budget_answered)
    case Unanswered{r}:
      by_reason(r, p, compaction_failed, autonomous_failed, budget_answered)

# after the command: how the wait ended
def by_wait(w: Wait, run: Run, p: Primary, compaction_failed: Bool, autonomous_failed: Bool, +budget_answered: Bool) -> Cause:
  match w:
    case Quiet{}:
      by_run(run, p, compaction_failed, autonomous_failed, budget_answered)
    case GaveUp{}:
      CGaveUp{}
    case BudgetDeadline{}:
      excuse(budget_answered, by_run(run, p, compaction_failed, autonomous_failed, budget_answered))

# the cause of the exit
def cause(f: Facts) -> Cause:
  match f:
    case Facts{command_failed, w, run, p, compaction_failed, autonomous_failed, budget_answered}:
      match command_failed:
        case True{}:
          CCommandFailed{}
        case False{}:
          by_wait(w, run, p, compaction_failed, autonomous_failed, budget_answered)

# the exit of a finished headless run
def decide(f: Facts) -> Verdict:
  verdict(cause(f))
