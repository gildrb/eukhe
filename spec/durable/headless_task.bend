# durable (spec): whether the exit of a headless run (`eukhe -p`,
# `--mode json`) stands for its task, stated without the rule of
# bend/headless_task.bend, and the wire of its entry
# (bend/ffi_headless_task.bend, crates/eukhe-bend/WIRE.md). The laws of
# area headless_task state T1-T3 and W6-W8 one property at a time, with
# the helpers below. A spec: the shipped code never calls it.
#
# T1: a run whose exit says it answered (headless_exit E1) after it acted
#     (a tool call with an effect, an edit or write, a spawned child) is
#     judged by its final answer: the core asks for the judge's reading
#     (task Ask, until Rust gives one), and an independent judge (one
#     model request without tools) reads whether the answer states work
#     of the task left. An answer that states work left is incomplete: it
#     exits 1. An answer the judge gave no verdict on (it could not run:
#     offline, rate-limited, a failed or stopped request, an unreadable
#     reply) is unjudged: it exits 3, its own code (0 is done, 1 a failure
#     or work left, 2 a usage error), never 0 and never 1.
# T2: a run that answered without acting (a question answered, reads
#     only) is never judged: no judge request, and its exit stands.
# T3: every other exit stands as headless_exit decided it, code and
#     cause: an answer that states no work left, a run that did not act,
#     every failure, a budget-limited run.
# W6: a request is the exit's cause, spelled as the headless_exit entry
#     replies it (W4), whether the run acted (a Bool), then the judge's
#     reading: 0 not asked | 1 no work left | 2 work left | 3 no verdict.
# W7: a reply is the code (Nat), then the task: 0 the exit stands |
#     1 incomplete | 2 unjudged | 3 ask the judge.
# W8: anything else is no request.

import Base
import ../../bend/headless_exit.bend as Hx
import ../../bend/headless_task.bend as Ht
import ../../bend/wire.bend as Wr
import ./headless_wire.bend as SpW

# The task (T1-T3)
# ----------------

# T1: the exit says the run answered
def exit_answered(c: Hx.Cause) -> Bool:
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
    case Hx.CBudgetLimited{}:
      False{}
    case Hx.CBudgetUnanswered{}:
      False{}

# T1: the judge read work left in the final answer
def report_left(r: Ht.Report) -> Bool:
  match r:
    case Ht.RUnasked{}:
      False{}
    case Ht.RDone{}:
      False{}
    case Ht.RLeft{}:
      True{}
    case Ht.RUnjudged{}:
      False{}

# T1: the judge was not asked
def report_unasked(r: Ht.Report) -> Bool:
  match r:
    case Ht.RUnasked{}:
      True{}
    case Ht.RDone{}:
      False{}
    case Ht.RLeft{}:
      False{}
    case Ht.RUnjudged{}:
      False{}

# T1: the judge gave no verdict on the final answer
def report_unjudged(r: Ht.Report) -> Bool:
  match r:
    case Ht.RUnasked{}:
      False{}
    case Ht.RDone{}:
      False{}
    case Ht.RLeft{}:
      False{}
    case Ht.RUnjudged{}:
      True{}

# the cause of the run's exit
def cause_of(f: Ht.Facts) -> Hx.Cause:
  match f:
    case Ht.Facts{c, a, r}:
      c

# T2: the run did not act
def unacted(f: Ht.Facts) -> Bool:
  match f:
    case Ht.Facts{c, a, r}:
      Bool.not(a)

# T1: the run answered after acting: its final answer is the judge's to
# read
def judged(f: Ht.Facts) -> Bool:
  match f:
    case Ht.Facts{c, a, r}:
      Bool.and(exit_answered(c), a)

# the judge's reading of the facts
def report_of(f: Ht.Facts) -> Ht.Report:
  match f:
    case Ht.Facts{c, a, r}:
      r

# T1: the run answered with work left: its final answer, which the judge
# reads, states work left
def unfinished(+f: Ht.Facts) -> Bool:
  Bool.and(judged(f), report_left(report_of(f)))

# T1: the judge reads the final answer and gave no verdict on it
def unjudged(+f: Ht.Facts) -> Bool:
  Bool.and(judged(f), report_unjudged(report_of(f)))

# T1: the judge reads the final answer and was not asked yet
def asks(+f: Ht.Facts) -> Bool:
  Bool.and(judged(f), report_unasked(report_of(f)))


# whether a task's exit is incomplete
def incomplete(v: Ht.Verdict) -> Bool:
  match v:
    case Ht.Verdict{n, t}:
      match t:
        case Ht.Stands{}:
          False{}
        case Ht.Incomplete{}:
          True{}
        case Ht.Unjudged{}:
          False{}
        case Ht.Ask{}:
          False{}

# whether a task's exit is unjudged
def unjudged_task(v: Ht.Verdict) -> Bool:
  match v:
    case Ht.Verdict{n, t}:
      match t:
        case Ht.Stands{}:
          False{}
        case Ht.Incomplete{}:
          False{}
        case Ht.Unjudged{}:
          True{}
        case Ht.Ask{}:
          False{}

# whether a task's exit asks for the judge's reading
def ask_task(v: Ht.Verdict) -> Bool:
  match v:
    case Ht.Verdict{n, t}:
      match t:
        case Ht.Stands{}:
          False{}
        case Ht.Incomplete{}:
          False{}
        case Ht.Unjudged{}:
          False{}
        case Ht.Ask{}:
          True{}

# T1: the code of an unjudged run
def unjudged_code() -> Nat:
  3n

# the code of a task's exit
def code_of(v: Ht.Verdict) -> Nat:
  match v:
    case Ht.Verdict{n, t}:
      n

# Requests and replies (W6-W7)
# ----------------------------

def w_report(r: Ht.Report, rest: String) -> String:
  match r:
    case Ht.RUnasked{}:
      Wr.put_nat(0n, rest)
    case Ht.RDone{}:
      Wr.put_nat(1n, rest)
    case Ht.RLeft{}:
      Wr.put_nat(2n, rest)
    case Ht.RUnjudged{}:
      Wr.put_nat(3n, rest)

# a request, then rest
def w_task_req(f: Ht.Facts, rest: String) -> String:
  match f:
    case Ht.Facts{c, a, r}:
      SpW.w_cause(c, Wr.put_bool(a, w_report(r, rest)))

def w_task(t: Ht.Task, rest: String) -> String:
  match t:
    case Ht.Stands{}:
      Wr.put_nat(0n, rest)
    case Ht.Incomplete{}:
      Wr.put_nat(1n, rest)
    case Ht.Unjudged{}:
      Wr.put_nat(2n, rest)
    case Ht.Ask{}:
      Wr.put_nat(3n, rest)

def w_verdict(v: Ht.Verdict, rest: String) -> String:
  match v:
    case Ht.Verdict{n, t}:
      Wr.put_nat(n, w_task(t, rest))

# The reader (W8)
# ---------------

def r_cause.failed(d: Wr.Dec<Hx.Reason>) -> Wr.Dec<Hx.Cause>:
  match d:
    case Wr.Got{r, s}:
      Wr.Got{Hx.CRunFailed{r}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def r_cause(d: Wr.Dec<Nat>) -> Wr.Dec<Hx.Cause>:
  match d:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          Wr.Got{Hx.CAnswered{}, s}
        case 1n:
          Wr.Got{Hx.CCommandFailed{}, s}
        case 2n:
          Wr.Got{Hx.CGaveUp{}, s}
        case 3n:
          r_cause.failed(SpW.r_reason(Wr.get_nat(s)))
        case 4n:
          Wr.Got{Hx.CProviderError{}, s}
        case 5n:
          Wr.Got{Hx.CAborted{}, s}
        case 6n:
          Wr.Got{Hx.CUnfinished{}, s}
        case 7n:
          Wr.Got{Hx.CSlashFailed{}, s}
        case 8n:
          Wr.Got{Hx.CCompactionFailed{}, s}
        case 9n:
          Wr.Got{Hx.CBudgetLimited{}, s}
        case 10n:
          Wr.Got{Hx.CBudgetUnanswered{}, s}
        case 11n+u:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

def r_report(d: Wr.Dec<Nat>) -> Wr.Dec<Ht.Report>:
  match d:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          Wr.Got{Ht.RUnasked{}, s}
        case 1n:
          Wr.Got{Ht.RDone{}, s}
        case 2n:
          Wr.Got{Ht.RLeft{}, s}
        case 3n:
          Wr.Got{Ht.RUnjudged{}, s}
        case 4n+u:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

def r_task.report(c: Hx.Cause, a: Bool, d: Wr.Dec<Ht.Report>) -> Wr.Dec<Ht.Facts>:
  match d:
    case Wr.Got{r, s}:
      Wr.Got{Ht.Facts{c, a, r}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def r_task.acted(c: Hx.Cause, d: Wr.Dec<Bool>) -> Wr.Dec<Ht.Facts>:
  match d:
    case Wr.Got{a, s}:
      r_task.report(c, a, r_report(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def r_task.cause(d: Wr.Dec<Hx.Cause>) -> Wr.Dec<Ht.Facts>:
  match d:
    case Wr.Got{c, s}:
      r_task.acted(c, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

# a request at the start of s, read with the wire's decoders
def r_task(s: String) -> Wr.Dec<Ht.Facts>:
  r_task.cause(r_cause(Wr.get_nat(s)))
