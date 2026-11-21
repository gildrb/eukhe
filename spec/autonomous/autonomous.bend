# autonomous (spec): what an autonomous run does at a final answer,
# stated without the rule of bend/autonomous.bend, and the wire of its
# entry (bend/ffi_autonomous.bend, crates/eukhe-bend/WIRE.md). The laws of
# area autonomous state A1-A6 and W1-W3 one property at a time, with the
# helpers below. A spec: the shipped code never calls it.
#
# A1: an autonomous run is continued with its continuation prompt exactly
#     when its final answer settled (a stop, a length cut, a tool use),
#     it has no check and its budget admits work.
# A2: with checks, the final answer is a claim the checks judge: a claim
#     that went back to the worker with its evidence holds the run (the
#     return continues it; the run adds no continuation of its own) while
#     the budget admits work; a claim that ended stops the run with the
#     claim's label (verified, failed, unverified, checks passed), whatever
#     the budget, unless A6 lets the run go on.
# A3: a budget that admits no more work (wrap-up, exhausted) stops the run
#     whose claim did not end: it is never continued past its limits.
# A4: a run that is not autonomous, and a final answer that broke (an
#     error, an abort), get nothing: no continuation, no hold, no stop.
# A5: the run has no limit of its own: no count of turns, tokens,
#     continuations or time enters the step.
# A6: a claim that ended passing (verified, checks passed) while the
#     budget admits work does not end a run whose final answer states work
#     left (the work-left rule, spec/agents/work_left.bend, holds for an
#     autonomous run too): the final-answer judge not read yet, the core
#     asks for its reading; read as work left, the run goes on with one
#     continuation that lists the work left. Read as no work left, or no
#     verdict, the claim stops the run with its label (A2).
# W1: a request is whether the run is autonomous (a Bool), the answer:
#     0 settled | 1 broken, the checks: 0 none | 1 returned | 2 ended then
#     the label (0 verified | 1 failed | 2 unverified | 3 passed), the
#     budget: 0 working | 1 short, then the judge's reading: 0 not read |
#     1 no work left | 2 work left | 3 no verdict.
# W2: a reply is the step: 0 off | 1 hold | 2 continue | 3 stop then the
#     cause: 0 checks then the label | 1 budget | 4 ask the judge | 5
#     finish (go on with the work left).
# W3: anything else is no request.

import Base
import ../../bend/verify.bend as V
import ../../bend/autonomous.bend as Au
import ../../bend/work_left.bend as Wl
import ../../bend/wire.bend as Wr
import ../agents/work_left.bend as SpL

# The facts (A1-A6)
# -----------------

# the run is autonomous
def on_of(f: Au.Facts) -> Bool:
  match f:
    case Au.Facts{on, a, c, b, r}:
      on

# A1, A4: the final answer settled
def settled(f: Au.Facts) -> Bool:
  match f:
    case Au.Facts{on, a, c, b, r}:
      match a:
        case Au.Settled{}:
          True{}
        case Au.Broken{}:
          False{}

# the checks at the answer
def checks_of(f: Au.Facts) -> Au.Checks:
  match f:
    case Au.Facts{on, a, c, b, r}:
      c

# A1: the run has no check
def unchecked(c: Au.Checks) -> Bool:
  match c:
    case Au.Unchecked{}:
      True{}
    case Au.Returned{}:
      False{}
    case Au.Ended{l}:
      False{}

# A2: the claim went back to the worker
def returned(c: Au.Checks) -> Bool:
  match c:
    case Au.Unchecked{}:
      False{}
    case Au.Returned{}:
      True{}
    case Au.Ended{l}:
      False{}

# A2: the claim ended
def ended(c: Au.Checks) -> Bool:
  match c:
    case Au.Unchecked{}:
      False{}
    case Au.Returned{}:
      False{}
    case Au.Ended{l}:
      True{}

# A1-A3: the budget admits work
def working(f: Au.Facts) -> Bool:
  match f:
    case Au.Facts{on, a, c, b, r}:
      match b:
        case Au.Working{}:
          True{}
        case Au.Short{}:
          False{}

# an autonomous run whose final answer settled
def live(+f: Au.Facts) -> Bool:
  Bool.and(on_of(f), settled(f))

# A1: the run is continued with its prompt
def continues(+f: Au.Facts) -> Bool:
  Bool.and(live(f), Bool.and(unchecked(checks_of(f)), working(f)))

# A2: the checks' return holds the run
def holds(+f: Au.Facts) -> Bool:
  Bool.and(live(f), Bool.and(returned(checks_of(f)), working(f)))

# A4: the run gets nothing
def off(+f: Au.Facts) -> Bool:
  Bool.not(live(f))

# A6: a label that passes: every check confirmed (verified, or checks
# passed unconfined)
def passing(l: V.Label) -> Bool:
  match l:
    case V.Verified{}:
      True{}
    case V.Failed{}:
      False{}
    case V.Unverified{}:
      False{}
    case V.Passed{}:
      True{}

# A6: the claim ended passing
def passed(c: Au.Checks) -> Bool:
  match c:
    case Au.Unchecked{}:
      False{}
    case Au.Returned{}:
      False{}
    case Au.Ended{l}:
      passing(l)

# A6: the final-answer judge's reading
def reading_of(f: Au.Facts) -> Wl.Reading:
  match f:
    case Au.Facts{on, a, c, b, r}:
      r

# A6: a claim that ended passing while the budget admits work, in an
# autonomous run whose answer settled
def passed_working(+f: Au.Facts) -> Bool:
  Bool.and(live(f), Bool.and(passed(checks_of(f)), working(f)))

# A6: the core asks for the judge's reading
def asks(+f: Au.Facts) -> Bool:
  Bool.and(passed_working(f), SpL.reading_unread(reading_of(f)))

# A6: the run goes on with the work the answer left
def finishes(+f: Au.Facts) -> Bool:
  Bool.and(passed_working(f), SpL.reading_left(reading_of(f)))

# A2, A6: the claim does not stop the run: the core asks, or the run
# finishes
def claim_goes_on(+f: Au.Facts) -> Bool:
  Bool.or(asks(f), finishes(f))

# The steps
# ---------

def is_off(t: Au.Step) -> Bool:
  match t:
    case Au.Off{}:
      True{}
    case Au.Hold{}:
      False{}
    case Au.Continue{}:
      False{}
    case Au.Stop{c}:
      False{}
    case Au.Ask{}:
      False{}
    case Au.Finish{}:
      False{}

def is_hold(t: Au.Step) -> Bool:
  match t:
    case Au.Off{}:
      False{}
    case Au.Hold{}:
      True{}
    case Au.Continue{}:
      False{}
    case Au.Stop{c}:
      False{}
    case Au.Ask{}:
      False{}
    case Au.Finish{}:
      False{}

def is_continue(t: Au.Step) -> Bool:
  match t:
    case Au.Off{}:
      False{}
    case Au.Hold{}:
      False{}
    case Au.Continue{}:
      True{}
    case Au.Stop{c}:
      False{}
    case Au.Ask{}:
      False{}
    case Au.Finish{}:
      False{}

def is_ask(t: Au.Step) -> Bool:
  match t:
    case Au.Off{}:
      False{}
    case Au.Hold{}:
      False{}
    case Au.Continue{}:
      False{}
    case Au.Stop{c}:
      False{}
    case Au.Ask{}:
      True{}
    case Au.Finish{}:
      False{}

def is_finish(t: Au.Step) -> Bool:
  match t:
    case Au.Off{}:
      False{}
    case Au.Hold{}:
      False{}
    case Au.Continue{}:
      False{}
    case Au.Stop{c}:
      False{}
    case Au.Ask{}:
      False{}
    case Au.Finish{}:
      True{}

# Requests and replies (W1-W2)
# ----------------------------

def w_answer(a: Au.Answer, rest: String) -> String:
  match a:
    case Au.Settled{}:
      Wr.put_nat(0n, rest)
    case Au.Broken{}:
      Wr.put_nat(1n, rest)

def w_label(l: V.Label, rest: String) -> String:
  match l:
    case V.Verified{}:
      Wr.put_nat(0n, rest)
    case V.Failed{}:
      Wr.put_nat(1n, rest)
    case V.Unverified{}:
      Wr.put_nat(2n, rest)
    case V.Passed{}:
      Wr.put_nat(3n, rest)

def w_checks(c: Au.Checks, rest: String) -> String:
  match c:
    case Au.Unchecked{}:
      Wr.put_nat(0n, rest)
    case Au.Returned{}:
      Wr.put_nat(1n, rest)
    case Au.Ended{l}:
      Wr.put_nat(2n, w_label(l, rest))

def w_budget(b: Au.Budget, rest: String) -> String:
  match b:
    case Au.Working{}:
      Wr.put_nat(0n, rest)
    case Au.Short{}:
      Wr.put_nat(1n, rest)

# a request, then rest
def w_req(f: Au.Facts, rest: String) -> String:
  match f:
    case Au.Facts{on, a, c, b, r}:
      Wr.put_bool(on, w_answer(a, w_checks(c, w_budget(b, SpL.w_reading(r, rest)))))

def w_cause(c: Au.Cause, rest: String) -> String:
  match c:
    case Au.ByChecks{l}:
      Wr.put_nat(0n, w_label(l, rest))
    case Au.ByBudget{}:
      Wr.put_nat(1n, rest)

# a reply, then rest
def w_step(t: Au.Step, rest: String) -> String:
  match t:
    case Au.Off{}:
      Wr.put_nat(0n, rest)
    case Au.Hold{}:
      Wr.put_nat(1n, rest)
    case Au.Continue{}:
      Wr.put_nat(2n, rest)
    case Au.Stop{c}:
      Wr.put_nat(3n, w_cause(c, rest))
    case Au.Ask{}:
      Wr.put_nat(4n, rest)
    case Au.Finish{}:
      Wr.put_nat(5n, rest)

# The reader (W3)
# ---------------

def r_answer(d: Wr.Dec<Nat>) -> Wr.Dec<Au.Answer>:
  match d:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          Wr.Got{Au.Settled{}, s}
        case 1n:
          Wr.Got{Au.Broken{}, s}
        case 2n+u:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

def r_label(d: Wr.Dec<Nat>) -> Wr.Dec<V.Label>:
  match d:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          Wr.Got{V.Verified{}, s}
        case 1n:
          Wr.Got{V.Failed{}, s}
        case 2n:
          Wr.Got{V.Unverified{}, s}
        case 3n:
          Wr.Got{V.Passed{}, s}
        case 4n+u:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

def r_checks.ended(d: Wr.Dec<V.Label>) -> Wr.Dec<Au.Checks>:
  match d:
    case Wr.Got{l, s}:
      Wr.Got{Au.Ended{l}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def r_checks(d: Wr.Dec<Nat>) -> Wr.Dec<Au.Checks>:
  match d:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          Wr.Got{Au.Unchecked{}, s}
        case 1n:
          Wr.Got{Au.Returned{}, s}
        case 2n:
          r_checks.ended(r_label(Wr.get_nat(s)))
        case 3n+u:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

def r_budget(d: Wr.Dec<Nat>) -> Wr.Dec<Au.Budget>:
  match d:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          Wr.Got{Au.Working{}, s}
        case 1n:
          Wr.Got{Au.Short{}, s}
        case 2n+u:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

def r_reading(d: Wr.Dec<Nat>) -> Wr.Dec<Wl.Reading>:
  match d:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          Wr.Got{Wl.Unread{}, s}
        case 1n:
          Wr.Got{Wl.Finished{}, s}
        case 2n:
          Wr.Got{Wl.Left{}, s}
        case 3n:
          Wr.Got{Wl.Unjudged{}, s}
        case 4n+u:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.reading(on: Bool, a: Au.Answer, c: Au.Checks, b: Au.Budget, d: Wr.Dec<Wl.Reading>) -> Wr.Dec<Au.Facts>:
  match d:
    case Wr.Got{r, s}:
      Wr.Got{Au.Facts{on, a, c, b, r}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.budget(on: Bool, a: Au.Answer, c: Au.Checks, d: Wr.Dec<Au.Budget>) -> Wr.Dec<Au.Facts>:
  match d:
    case Wr.Got{b, s}:
      r_req.reading(on, a, c, b, r_reading(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.checks(on: Bool, a: Au.Answer, d: Wr.Dec<Au.Checks>) -> Wr.Dec<Au.Facts>:
  match d:
    case Wr.Got{c, s}:
      r_req.budget(on, a, c, r_budget(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.answer(on: Bool, d: Wr.Dec<Au.Answer>) -> Wr.Dec<Au.Facts>:
  match d:
    case Wr.Got{a, s}:
      r_req.checks(on, a, r_checks(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.on(d: Wr.Dec<Bool>) -> Wr.Dec<Au.Facts>:
  match d:
    case Wr.Got{on, s}:
      r_req.answer(on, r_answer(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

# a request at the start of s, read with the wire's decoders
def r_req(s: String) -> Wr.Dec<Au.Facts>:
  r_req.on(Wr.get_bool(s))
