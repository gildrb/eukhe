# headless_settle: when a headless run (`eukhe -p`, `--mode json`,
# `--mode rpc`) may stop waiting after its prompt's turn ended. The turn
# that answered is not the end of the work: background jobs, kernel
# background commands, subagents and workflow runs it started settle
# later and wake the conversation with a notice. The run waits until
# nothing is left, or gives up when its stated wait limit elapsed.
# Entry: bend/ffi_headless_settle.bend (Rust: eukhe-bend
# rules/headless.rs `settle`). Laws: laws/headless_settle.bend.
#
# - Finished: the main conversation is idle (no run, no queued input),
#   no job, kernel job, subagent or workflow run is pending, no settle
#   notice is being admitted, and the pending-work read did not fail.
# - Otherwise GiveUp once the wait limit elapsed, else Waiting.
#
# Pure: no IO, no @unsafe.

import Base

# Types
# -----

# the facts of one check: the main conversation runs or holds queued
# input (busy), the counts of pending work, the settle notices being
# admitted right now (wakes), the pending-work read failed (unknown), the
# wait limit elapsed (limit_hit)
type Facts is Data:
  Facts{busy: Bool, jobs: Nat, kernel_jobs: Nat, children: Nat, workflow_runs: Nat, wakes: Nat, unknown: Bool, limit_hit: Bool}

# what the run does next: stop (nothing is left), wait, or give up
type Settle is Data:
  Finished{}
  Waiting{}
  GiveUp{}

# The rule
# --------

# some work of a kind counted n is pending
def some(n: Nat) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n+p:
      True{}

# stop when nothing is pending; else give up at the limit, else wait
def decide(pending: Bool, limit_hit: Bool) -> Settle:
  match pending:
    case False{}:
      Finished{}
    case True{}:
      match limit_hit:
        case True{}:
          GiveUp{}
        case False{}:
          Waiting{}

# what the run does next, given the facts of this check
def settle(f: Facts) -> Settle:
  match f:
    case Facts{busy, jobs, kernel_jobs, children, workflow_runs, wakes, unknown, limit_hit}:
      decide(Bool.or(busy, Bool.or(some(jobs), Bool.or(some(kernel_jobs), Bool.or(some(children), Bool.or(some(workflow_runs), Bool.or(some(wakes), unknown)))))), limit_hit)
