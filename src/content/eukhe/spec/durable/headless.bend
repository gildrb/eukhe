# durable (spec): the two decisions of a headless run (`eukhe -p`,
# `--mode json`, `--mode rpc`), restated without the rules of
# bend/headless_settle.bend and bend/headless_exit.bend: when the run may
# stop waiting for the work its turn started (area headless_settle), and
# its process exit code (area headless_exit). spec/durable/headless_wire.bend
# holds the wire of the two entries. The laws of the two areas state that
# the rules refine it. A spec: the shipped code never calls it.
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

# Settle (Q1-Q2)
# --------------

# Q1: nothing runs, nothing is pending, nothing is unknown
def quiet(f: Hs.Facts) -> Bool:
  match f:
    case Hs.Facts{b, j, k, c, w, x, u, l}:
      Bool.and(Bool.not(b), Bool.and(Nat.is_eq(j, 0n), Bool.and(Nat.is_eq(k, 0n), Bool.and(Nat.is_eq(c, 0n), Bool.and(Nat.is_eq(w, 0n), Bool.and(Nat.is_eq(x, 0n), Bool.not(u)))))))

# the wait limit elapsed
def limit_hit(f: Hs.Facts) -> Bool:
  match f:
    case Hs.Facts{b, j, k, c, w, x, u, l}:
      l

def settle_spec.pick(q: Bool, l: Bool) -> Hs.Settle:
  match q:
    case True{}:
      Hs.Finished{}
    case False{}:
      match l:
        case True{}:
          Hs.GiveUp{}
        case False{}:
          Hs.Waiting{}

# Q2: finished when quiet; else give up at the limit; else wait
def settle_spec(+f: Hs.Facts) -> Hs.Settle:
  settle_spec.pick(quiet(f), limit_hit(f))

# Exit (E1-E2)
# ------------

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

# the first failure of the list, else answered
def first(xs: List<&2, Maybe<&2, Hx.Cause>>) -> Hx.Cause:
  match xs:
    case Nil{}:
      Hx.CAnswered{}
    case Con{m, rest}:
      match m:
        case None{}:
          first(rest)
        case Some{c}:
          c

# the failures in the order of E1
def failures(f: Hx.Facts) -> List<&2, Maybe<&2, Hx.Cause>>:
  match f:
    case Hx.Facts{cf, gu, run, p, c, a}:
      [when(cf, Hx.CCommandFailed{}), when(gu, Hx.CGaveUp{}), run_cause(run), primary_cause(p), when(c, Hx.CCompactionFailed{}), when(a, Hx.CAutonomousFailed{})]

# E1: the cause of the exit
def cause_spec(f: Hx.Facts) -> Hx.Cause:
  first(failures(f))

# the run answered
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

def code_spec(b: Bool) -> Nat:
  match b:
    case True{}:
      0n
    case False{}:
      1n

# E1-E2: the exit: the code of the cause, and the cause
def exit_spec(f: Hx.Facts) -> Hx.Verdict:
  +c = cause_spec(f)
  Hx.Verdict{code_spec(answered(c)), c}
