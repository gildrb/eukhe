# ffi_autonomous: the entry of the compiled Bend core that decides what
# an autonomous run does at a final answer (bend/autonomous.bend; Rust:
# eukhe-bend rules/autonomous.rs). Grammar: crates/eukhe-bend/WIRE.md.
#
#   request  whether the run is autonomous (a Bool), the answer: 0 settled
#            | 1 broken, the checks: 0 none | 1 returned | 2 ended then
#            the label (0 verified | 1 failed | 2 unverified | 3 passed),
#            the budget: 0 working | 1 short, the final-answer judge's
#            reading: 0 not read | 1 no work left | 2 work left | 3 no
#            verdict
#   reply    the step: 0 off | 1 hold | 2 continue | 3 stop then the
#            cause: 0 checks then the label | 1 budget | 4 ask the judge
#            | 5 finish (go on with the work left)
#
# Malformed input, or input left after the request, answers
# `E autonomous: malformed request`, never a default.
# Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./verify.bend as V
import ./autonomous.bend as Au
import ./work_left.bend as Wl

# Requests
# --------

def get_answer(r: W.Dec<Nat>) -> W.Dec<Au.Answer>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          W.Got{Au.Settled{}, s}
        case 1n:
          W.Got{Au.Broken{}, s}
        case 2n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_label(r: W.Dec<Nat>) -> W.Dec<V.Label>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          W.Got{V.Verified{}, s}
        case 1n:
          W.Got{V.Failed{}, s}
        case 2n:
          W.Got{V.Unverified{}, s}
        case 3n:
          W.Got{V.Passed{}, s}
        case 4n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_checks.ended(d: W.Dec<V.Label>) -> W.Dec<Au.Checks>:
  match d:
    case W.Got{l, s}:
      W.Got{Au.Ended{l}, s}
    case W.Bad{}:
      W.Bad{}

def get_checks(r: W.Dec<Nat>) -> W.Dec<Au.Checks>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          W.Got{Au.Unchecked{}, s}
        case 1n:
          W.Got{Au.Returned{}, s}
        case 2n:
          get_checks.ended(get_label(W.get_nat(s)))
        case 3n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_budget(r: W.Dec<Nat>) -> W.Dec<Au.Budget>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          W.Got{Au.Working{}, s}
        case 1n:
          W.Got{Au.Short{}, s}
        case 2n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_reading(r: W.Dec<Nat>) -> W.Dec<Wl.Reading>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          W.Got{Wl.Unread{}, s}
        case 1n:
          W.Got{Wl.Finished{}, s}
        case 2n:
          W.Got{Wl.Left{}, s}
        case 3n:
          W.Got{Wl.Unjudged{}, s}
        case 4n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_facts.reading(on: Bool, a: Au.Answer, c: Au.Checks, b: Au.Budget, d: W.Dec<Wl.Reading>) -> W.Dec<Au.Facts>:
  match d:
    case W.Got{r, s}:
      W.Got{Au.Facts{on, a, c, b, r}, s}
    case W.Bad{}:
      W.Bad{}

def get_facts.budget(on: Bool, a: Au.Answer, c: Au.Checks, d: W.Dec<Au.Budget>) -> W.Dec<Au.Facts>:
  match d:
    case W.Got{b, s}:
      get_facts.reading(on, a, c, b, get_reading(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_facts.checks(on: Bool, a: Au.Answer, d: W.Dec<Au.Checks>) -> W.Dec<Au.Facts>:
  match d:
    case W.Got{c, s}:
      get_facts.budget(on, a, c, get_budget(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_facts.answer(on: Bool, d: W.Dec<Au.Answer>) -> W.Dec<Au.Facts>:
  match d:
    case W.Got{a, s}:
      get_facts.checks(on, a, get_checks(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_facts.on(d: W.Dec<Bool>) -> W.Dec<Au.Facts>:
  match d:
    case W.Got{on, s}:
      get_facts.answer(on, get_answer(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

# the request at the start of s
def get_facts(s: String) -> W.Dec<Au.Facts>:
  get_facts.on(W.get_bool(s))

# Replies
# -------

def put_label(l: V.Label, rest: String) -> String:
  match l:
    case V.Verified{}:
      W.put_nat(0n, rest)
    case V.Failed{}:
      W.put_nat(1n, rest)
    case V.Unverified{}:
      W.put_nat(2n, rest)
    case V.Passed{}:
      W.put_nat(3n, rest)

def put_cause(c: Au.Cause, rest: String) -> String:
  match c:
    case Au.ByChecks{l}:
      W.put_nat(0n, put_label(l, rest))
    case Au.ByBudget{}:
      W.put_nat(1n, rest)

# the spelling of a step
def put_step(t: Au.Step, rest: String) -> String:
  match t:
    case Au.Off{}:
      W.put_nat(0n, rest)
    case Au.Hold{}:
      W.put_nat(1n, rest)
    case Au.Continue{}:
      W.put_nat(2n, rest)
    case Au.Stop{c}:
      W.put_nat(3n, put_cause(c, rest))
    case Au.Ask{}:
      W.put_nat(4n, rest)
    case Au.Finish{}:
      W.put_nat(5n, rest)

def ffi.done(f: Au.Facts, end: Bool) -> String:
  match end:
    case True{}:
      put_step(Au.decide(f), "")
    case False{}:
      W.err("autonomous: malformed request")

def ffi.got(r: W.Dec<Au.Facts>) -> String:
  match r:
    case W.Got{f, +s}:
      ffi.done(f, W.end(s))
    case W.Bad{}:
      W.err("autonomous: malformed request")

# the entry: decode the facts, answer the step
def ffi(input: String) -> String:
  ffi.got(get_facts(input))
