# work_left: whether a run goes on past a final answer that leaves task
# work undone. The Rust code (crates/eukhe-core/src/durable/directors/
# work_left.rs, an `on_yield` hook after the Director stack's step) asks
# it at each final answer the Director stack, the autonomous run and the
# loop did not continue. Nobody watches a run: an answer that asks the
# user for leave to do part of the task, offers to do the rest, or asks
# how to go on hands the work back to a person who is not there.
#
# - The answer is the run's to judge when nothing else owns the boundary:
#   no autonomous run or loop drives the run, no input is queued (user
#   input, unsettled children or workflow runs), the run acted since the
#   user's last message (a tool call with an effect), the session's budget
#   admits more work, the progress check (bend/progress.bend `judge`,
#   directors.stallSteps) goes on, and the Director loop has a step left.
# - Such an answer not read yet: the core answers Ask, and Rust asks the
#   final-answer judge (one model request, no tools, the answer alone),
#   then decides again with its reading.
# - Work left: the run goes on with one harness continuation, which costs
#   one step of the loop. An answer that states no work left, and one the
#   judge gave no verdict on, stand: the run yields.
#
# Entry: bend/ffi_work_left.bend (Rust: eukhe-bend rules/work_left.rs).
# Laws: laws/work_left.bend.
#
# Pure: no IO, no @unsafe.

import Base
import ./progress.bend as Pg

# Types
# -----

# the judge's reading of the final answer: not read yet, no work left,
# work left, or no verdict (its request failed or was stopped, its reply
# unreadable)
type Reading is Data:
  Unread{}
  Finished{}
  Left{}
  Unjudged{}

# the facts at a final answer: whether an autonomous run or a loop drives
# the run; whether input is queued; whether the run acted since the user's
# last message; whether the session's budget admits more work; the
# progress check's verdict; the steps the Director loop has left; the
# judge's reading
type Facts is Data:
  Facts{driven: Bool, queued: Bool, acted: Bool, funded: Bool, stall: Pg.Goal, left: Nat, reading: Reading}

# what the run does: go on with one continuation (the loop's steps left
# after it), yield (the final answer stands), or ask the judge first
type Step is Data:
  Continue{left: Nat}
  Yield{}
  Ask{}

# The rule
# --------

# what the reading makes of an answer the run may go on from, m steps left
# after a continuation
def by_reading(m: Nat, r: Reading) -> Step:
  match r:
    case Unread{}:
      Ask{}
    case Finished{}:
      Yield{}
    case Left{}:
      Continue{m}
    case Unjudged{}:
      Yield{}

# a run with n loop steps left: none left yields
def by_steps(n: Nat, r: Reading) -> Step:
  match n:
    case 0n:
      Yield{}
    case 1n+m:
      by_reading(m, r)

def decide.at(open: Bool, n: Nat, r: Reading) -> Step:
  match open:
    case True{}:
      by_steps(n, r)
    case False{}:
      Yield{}

# the step at a final answer
def decide(f: Facts) -> Step:
  match f:
    case Facts{d, q, a, b, s, n, r}:
      decide.at(Bool.and(Bool.not(d), Bool.and(Bool.not(q), Bool.and(a, Bool.and(b, Bool.not(Pg.Goal.stopped(s)))))), n, r)
