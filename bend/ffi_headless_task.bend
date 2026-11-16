# ffi_headless_task: the entry of the compiled Bend core that decides
# whether the exit of a headless run stands for its task
# (bend/headless_task.bend; Rust: eukhe-bend rules/headless.rs `task`).
# Grammar: crates/eukhe-bend/WIRE.md.
#
#   request  the exit's cause as ffi_headless_exit replies it (0 answered
#            .. 11 budget unanswered; 3 run failed is followed by its
#            reason), the goal: 0 none | 1 complete | 2 open, then the
#            judge's reading of the final answer: 0 not asked | 1 no
#            work left | 2 work left | 3 no verdict
#   reply    the code (Nat), then the task: 0 the exit stands |
#            1 incomplete | 2 unjudged
#
# Malformed input, or input left after the request, answers
# `E headless_task: malformed request`, never a default.
# Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./headless_exit.bend as Hx
import ./ffi_headless_exit.bend as FHx
import ./headless_task.bend as Ht

# Requests
# --------

def get_cause.failed(d: W.Dec<Hx.Reason>) -> W.Dec<Hx.Cause>:
  match d:
    case W.Got{r, s}:
      W.Got{Hx.CRunFailed{r}, s}
    case W.Bad{}:
      W.Bad{}

def get_cause(r: W.Dec<Nat>) -> W.Dec<Hx.Cause>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          W.Got{Hx.CAnswered{}, s}
        case 1n:
          W.Got{Hx.CCommandFailed{}, s}
        case 2n:
          W.Got{Hx.CGaveUp{}, s}
        case 3n:
          get_cause.failed(FHx.get_reason(W.get_nat(s)))
        case 4n:
          W.Got{Hx.CProviderError{}, s}
        case 5n:
          W.Got{Hx.CAborted{}, s}
        case 6n:
          W.Got{Hx.CUnfinished{}, s}
        case 7n:
          W.Got{Hx.CSlashFailed{}, s}
        case 8n:
          W.Got{Hx.CCompactionFailed{}, s}
        case 9n:
          W.Got{Hx.CAutonomousFailed{}, s}
        case 10n:
          W.Got{Hx.CBudgetLimited{}, s}
        case 11n:
          W.Got{Hx.CBudgetUnanswered{}, s}
        case 12n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_goal(r: W.Dec<Nat>) -> W.Dec<Ht.Goal>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          W.Got{Ht.NoGoal{}, s}
        case 1n:
          W.Got{Ht.Complete{}, s}
        case 2n:
          W.Got{Ht.Open{}, s}
        case 3n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_report(r: W.Dec<Nat>) -> W.Dec<Ht.Report>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          W.Got{Ht.RUnasked{}, s}
        case 1n:
          W.Got{Ht.RDone{}, s}
        case 2n:
          W.Got{Ht.RLeft{}, s}
        case 3n:
          W.Got{Ht.RUnjudged{}, s}
        case 4n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_facts.report(c: Hx.Cause, g: Ht.Goal, d: W.Dec<Ht.Report>) -> W.Dec<Ht.Facts>:
  match d:
    case W.Got{r, s}:
      W.Got{Ht.Facts{c, g, r}, s}
    case W.Bad{}:
      W.Bad{}

def get_facts.goal(c: Hx.Cause, d: W.Dec<Ht.Goal>) -> W.Dec<Ht.Facts>:
  match d:
    case W.Got{g, s}:
      get_facts.report(c, g, get_report(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_facts.cause(d: W.Dec<Hx.Cause>) -> W.Dec<Ht.Facts>:
  match d:
    case W.Got{c, s}:
      get_facts.goal(c, get_goal(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

# the request at the start of s
def get_facts(s: String) -> W.Dec<Ht.Facts>:
  get_facts.cause(get_cause(W.get_nat(s)))

# Replies
# -------

def put_task(t: Ht.Task, rest: String) -> String:
  match t:
    case Ht.Stands{}:
      W.put_nat(0n, rest)
    case Ht.Incomplete{}:
      W.put_nat(1n, rest)
    case Ht.Unjudged{}:
      W.put_nat(2n, rest)

# the spelling of a task's exit: its code, then the task
def put_verdict(v: Ht.Verdict, rest: String) -> String:
  match v:
    case Ht.Verdict{n, t}:
      W.put_nat(n, put_task(t, rest))

def ffi.done(f: Ht.Facts, end: Bool) -> String:
  match end:
    case True{}:
      put_verdict(Ht.decide(f), "")
    case False{}:
      W.err("headless_task: malformed request")

def ffi.got(r: W.Dec<Ht.Facts>) -> String:
  match r:
    case W.Got{f, +s}:
      ffi.done(f, W.end(s))
    case W.Bad{}:
      W.err("headless_task: malformed request")

# the entry: decode the facts, answer the task's exit
def ffi(input: String) -> String:
  ffi.got(get_facts(input))
