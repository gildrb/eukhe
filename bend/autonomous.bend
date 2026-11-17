# autonomous: what an autonomous run does at a final answer. An
# autonomous run is one the principal set to go on without a human
# (`--auto`, `/auto`, a client's create config): after each final answer
# the harness continues it until its checks end the claim, the budget
# admits no more work or the principal stops it. With checks every final
# answer is a claim (bend/verify.bend): a refuted or broken claim goes
# back to the worker with its evidence (the verifier's return continues
# the run), and a claim that ended stops the run with its label. Without
# checks the run is continued with its continuation prompt. The run has
# no limit of its own: the run's budget (bend/budget.bend,
# bend/limits.bend) is its only one. A failed or aborted answer, or a run
# that is not autonomous, gets nothing from this rule. Entry:
# bend/ffi_autonomous.bend (Rust: eukhe-bend rules/autonomous.rs). Laws:
# laws/autonomous.bend. Spec: spec/autonomous/autonomous.bend.
#
# Pure: no IO, no @unsafe.

import Base
import ./verify.bend as V

# Types
# -----

# how the answer ended: settled (a stop, a length cut, a tool use) or
# broken (an error, an abort)
type Answer is Data:
  Settled{}
  Broken{}

# the run's checks at this answer: none, the claim went back to the
# worker with its evidence, or the claim ended with a label
type Checks is Data:
  Unchecked{}
  Returned{}
  Ended{label: V.Label}

# the run's budget: it admits work, or it does not (wrap-up, exhausted)
type Budget is Data:
  Working{}
  Short{}

# the facts of one final answer: whether the run is autonomous, how the
# answer ended, the checks, the budget
type Facts is Data:
  Facts{on: Bool, answer: Answer, checks: Checks, budget: Budget}

# why an autonomous run stopped: its checks ended the claim with a
# label, or the budget admits no more work
type Cause is Data:
  ByChecks{label: V.Label}
  ByBudget{}

# what the run does: nothing (not autonomous, or the answer broke); hold
# (the checks' return continues the run); continue with the continuation
# prompt; stop with its cause
type Step is Data:
  Off{}
  Hold{}
  Continue{}
  Stop{cause: Cause}

# The rule
# --------

# the step of a run whose claim did not end: go on while the budget
# admits work
def go(s: Step, b: Budget) -> Step:
  match b:
    case Working{}:
      s
    case Short{}:
      Stop{ByBudget{}}

# the step of an autonomous run whose answer settled
def settled(c: Checks, b: Budget) -> Step:
  match c:
    case Unchecked{}:
      go(Continue{}, b)
    case Returned{}:
      go(Hold{}, b)
    case Ended{l}:
      Stop{ByChecks{l}}

# the step of an autonomous run
def answered(a: Answer, c: Checks, b: Budget) -> Step:
  match a:
    case Settled{}:
      settled(c, b)
    case Broken{}:
      Off{}

# the step at a final answer
def decide(f: Facts) -> Step:
  match f:
    case Facts{on, a, c, b}:
      match on:
        case True{}:
          answered(a, c, b)
        case False{}:
          Off{}
