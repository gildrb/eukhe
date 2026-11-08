# headless_exit: the process exit code of a headless run (`eukhe -p`,
# `--mode json`) and its cause. A run that did not answer, or answered
# with a failure, exits nonzero, so a script or CI job never reads a
# failed run as done. Entry: bend/ffi_headless_exit.bend (Rust: eukhe-bend
# rules/headless.rs `exit`). Laws: laws/headless_exit.bend.
#
# The cause is the first failure that holds, in this order: a session
# command prompt failed; the settle wait gave up at its limit; the last
# run settled unanswered for a failure (a model error, the run limit, no
# model, a forced tool, a fault, an abort, another reason; a reset, a
# stale run and a withdrawn input are no failure of the run); the
# terminal transcript entry is a provider error, an aborted reply, an
# unfinished reply (a tool use, a pending or deferred turn) or a failed
# slash command; a compaction failed; an autonomous turn failed. With
# none, the run answered. The code is 0 for an answered run, else 1.
#
# Pure: no IO, no @unsafe.

import Base

# Types
# -----

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

# how the last run settled
type Run is Data:
  NoRun{}
  Answered{}
  Unanswered{reason: Reason}

# the terminal transcript entry: none, an assistant reply that stopped
# (stop, length), one left unfinished (tool use, pending, deferred), a
# provider error, an aborted reply, a slash command that succeeded or
# failed
type Primary is Data:
  PNothing{}
  PAnswer{}
  PUnfinished{}
  PProviderError{}
  PAborted{}
  PSlashOk{}
  PSlashFailed{}

# the facts of a finished headless run
type Facts is Data:
  Facts{command_failed: Bool, gave_up: Bool, run: Run, primary: Primary, compaction_failed: Bool, autonomous_failed: Bool}

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

# the exit: the process code and its cause
type Verdict is Data:
  Verdict{code: Nat, cause: Cause}

# The rule
# --------

# the code of a cause: 0 for an answered run, 1 for every failure
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

# the exit of a cause
def verdict(+c: Cause) -> Verdict:
  Verdict{code(c), c}

# after the transcript: a failed compaction, then a failed autonomous turn
def by_flags(compaction_failed: Bool, autonomous_failed: Bool) -> Cause:
  match compaction_failed:
    case True{}:
      CCompactionFailed{}
    case False{}:
      match autonomous_failed:
        case True{}:
          CAutonomousFailed{}
        case False{}:
          CAnswered{}

# after the run: the terminal transcript entry
def by_primary(p: Primary, compaction_failed: Bool, autonomous_failed: Bool) -> Cause:
  match p:
    case PNothing{}:
      by_flags(compaction_failed, autonomous_failed)
    case PAnswer{}:
      by_flags(compaction_failed, autonomous_failed)
    case PUnfinished{}:
      CUnfinished{}
    case PProviderError{}:
      CProviderError{}
    case PAborted{}:
      CAborted{}
    case PSlashOk{}:
      by_flags(compaction_failed, autonomous_failed)
    case PSlashFailed{}:
      CSlashFailed{}

# an unanswered run: its reason, unless the reason is no failure of the run
def by_reason(r: Reason, p: Primary, compaction_failed: Bool, autonomous_failed: Bool) -> Cause:
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
      by_primary(p, compaction_failed, autonomous_failed)
    case Stale{}:
      by_primary(p, compaction_failed, autonomous_failed)
    case Withdrawn{}:
      by_primary(p, compaction_failed, autonomous_failed)
    case Other{}:
      CRunFailed{Other{}}

# after the wait: the last run's settlement
def by_run(run: Run, p: Primary, compaction_failed: Bool, autonomous_failed: Bool) -> Cause:
  match run:
    case NoRun{}:
      by_primary(p, compaction_failed, autonomous_failed)
    case Answered{}:
      by_primary(p, compaction_failed, autonomous_failed)
    case Unanswered{r}:
      by_reason(r, p, compaction_failed, autonomous_failed)

# the cause of the exit
def cause(f: Facts) -> Cause:
  match f:
    case Facts{command_failed, gave_up, run, p, compaction_failed, autonomous_failed}:
      match command_failed:
        case True{}:
          CCommandFailed{}
        case False{}:
          match gave_up:
            case True{}:
              CGaveUp{}
            case False{}:
              by_run(run, p, compaction_failed, autonomous_failed)

# the exit of a finished headless run
def decide(f: Facts) -> Verdict:
  verdict(cause(f))
