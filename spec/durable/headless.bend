# durable (spec): the two decisions of a headless run (`eukhe -p`,
# `--mode json`, `--mode rpc`), stated without the rules of
# bend/headless_settle.bend and bend/headless_exit.bend: when the run may
# stop waiting for the work its turn started (area headless_settle), and
# its process exit code (area headless_exit). spec/durable/headless_wire.bend
# holds the wire of the two entries. The laws of the two areas state Q1-Q2
# and E1-E2 over the facts, one property at a time, with the helpers
# below. A spec: the shipped code never calls it.
#
# Q1: the run is quiet when the main conversation neither runs nor holds
#     queued input, every count of pending work (session jobs, kernel
#     background commands, subagents, workflow runs, settle notices being
#     admitted) is zero, and the pending-work read did not fail.
# Q2: a quiet run is finished. A run that is not quiet gives up once the
#     wait limit elapsed, and waits before.
# E1: the cause of the exit is the first failure that holds, in this
#     order: a failed session command; a wait that gave up at its limit
#     or ended at the time budget's deadline; a run that settled
#     unanswered for a failure (every reason but a reset, a stale run and
#     a withdrawn input); a terminal transcript entry that is a provider
#     error, a budget refusal, an aborted reply, an unfinished reply or a
#     failed slash command; a failed compaction; a failed autonomous turn.
#     Without one the run answered. When the agent's final answer from
#     the budget's reserve was delivered, the facts a used-up budget
#     leaves (the wait at the deadline, a run or a terminal entry the
#     budget refused: budget-unanswered, excused) are no failure, and a
#     run without another failure is budget-limited.
# E2: the exit code is 0 for an answered or budget-limited run, 1 for
#     every failure.

import Base
import ../../bend/headless_settle.bend as Hs
import ../../bend/headless_exit.bend as Hx

# Settle (Q1)
# -----------

# Q1: nothing runs, nothing is pending, nothing is unknown
def quiet(f: Hs.Facts) -> Bool:
  match f:
    case Hs.Facts{b, j, k, c, w, x, u, l}:
      Bool.and(Bool.not(b), Bool.and(Nat.is_eq(j, 0n), Bool.and(Nat.is_eq(k, 0n), Bool.and(Nat.is_eq(c, 0n), Bool.and(Nat.is_eq(w, 0n), Bool.and(Nat.is_eq(x, 0n), Bool.not(u)))))))

# Exit (E1)
# ---------

# a cause, when its failure holds
def when(b: Bool, c: Hx.Cause) -> Maybe<&2, Hx.Cause>:
  match b:
    case True{}:
      Some{c}
    case False{}:
      None{}

# the reasons that are a failure of the run by their own reason (all but
# reset, stale, withdrawn, and a budget refusal: run_cause)
def run_fails(r: Hx.Reason) -> Bool:
  match r:
    case Hx.ModelError{}:
      True{}
    case Hx.RunLimit{}:
      True{}
    case Hx.NoModel{}:
      True{}
    case Hx.ForcedTool{}:
      True{}
    case Hx.Faulted{}:
      True{}
    case Hx.Aborted{}:
      True{}
    case Hx.Reset{}:
      False{}
    case Hx.Stale{}:
      False{}
    case Hx.Withdrawn{}:
      False{}
    case Hx.Other{}:
      True{}
    case Hx.BudgetRefused{}:
      False{}

# the failure of a run unanswered for r, if it is one
def reason_cause(+r: Hx.Reason) -> Maybe<&2, Hx.Cause>:
  match r:
    case Hx.BudgetRefused{}:
      Some{Hx.CBudgetUnanswered{}}
    case Hx.ModelError{}:
      when(run_fails(Hx.ModelError{}), Hx.CRunFailed{Hx.ModelError{}})
    case Hx.RunLimit{}:
      when(run_fails(Hx.RunLimit{}), Hx.CRunFailed{Hx.RunLimit{}})
    case Hx.NoModel{}:
      when(run_fails(Hx.NoModel{}), Hx.CRunFailed{Hx.NoModel{}})
    case Hx.ForcedTool{}:
      when(run_fails(Hx.ForcedTool{}), Hx.CRunFailed{Hx.ForcedTool{}})
    case Hx.Faulted{}:
      when(run_fails(Hx.Faulted{}), Hx.CRunFailed{Hx.Faulted{}})
    case Hx.Aborted{}:
      when(run_fails(Hx.Aborted{}), Hx.CRunFailed{Hx.Aborted{}})
    case Hx.Reset{}:
      when(run_fails(Hx.Reset{}), Hx.CRunFailed{Hx.Reset{}})
    case Hx.Stale{}:
      when(run_fails(Hx.Stale{}), Hx.CRunFailed{Hx.Stale{}})
    case Hx.Withdrawn{}:
      when(run_fails(Hx.Withdrawn{}), Hx.CRunFailed{Hx.Withdrawn{}})
    case Hx.Other{}:
      when(run_fails(Hx.Other{}), Hx.CRunFailed{Hx.Other{}})

# the failure of the last run, if it failed
def run_cause(run: Hx.Run) -> Maybe<&2, Hx.Cause>:
  match run:
    case Hx.NoRun{}:
      None{}
    case Hx.Answered{}:
      None{}
    case Hx.Unanswered{r}:
      reason_cause(r)

# the failure of the terminal transcript entry, if it is one
def primary_cause(p: Hx.Primary) -> Maybe<&2, Hx.Cause>:
  match p:
    case Hx.PNothing{}:
      None{}
    case Hx.PAnswer{}:
      None{}
    case Hx.PUnfinished{}:
      Some{Hx.CUnfinished{}}
    case Hx.PProviderError{}:
      Some{Hx.CProviderError{}}
    case Hx.PAborted{}:
      Some{Hx.CAborted{}}
    case Hx.PSlashOk{}:
      None{}
    case Hx.PSlashFailed{}:
      Some{Hx.CSlashFailed{}}
    case Hx.PBudgetRefused{}:
      Some{Hx.CBudgetUnanswered{}}

# the failure of how the wait ended, if it is one
def wait_cause(w: Hx.Wait) -> Maybe<&2, Hx.Cause>:
  match w:
    case Hx.Quiet{}:
      None{}
    case Hx.GaveUp{}:
      Some{Hx.CGaveUp{}}
    case Hx.BudgetDeadline{}:
      Some{Hx.CBudgetUnanswered{}}

# a failure the delivered final answer from the budget's reserve excuses:
# the budget ended the run, after its answer
def excused(c: Hx.Cause) -> Bool:
  match c:
    case Hx.CAnswered{}:
      False{}
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
      True{}
