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
#     order: a failed session command; a wait that gave up; a run that
#     settled unanswered for a failure (every reason but a reset, a stale
#     run and a withdrawn input); a terminal transcript entry that is a
#     provider error, an aborted reply, an unfinished reply or a failed
#     slash command; a failed compaction; a failed autonomous turn.
#     Without one the run answered.
# E2: the exit code is 0 for an answered run, 1 for every failure.

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

# the reasons that are a failure of the run (all but reset, stale,
# withdrawn)
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

# the failure of the last run, if it failed
def run_cause(run: Hx.Run) -> Maybe<&2, Hx.Cause>:
  match run:
    case Hx.NoRun{}:
      None{}
    case Hx.Answered{}:
      None{}
    case Hx.Unanswered{+r}:
      when(run_fails(r), Hx.CRunFailed{r})

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
