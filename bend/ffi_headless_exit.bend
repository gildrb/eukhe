# ffi_headless_exit: the entry of the compiled Bend core that decides the
# exit code of a headless run (bend/headless_exit.bend; Rust: eukhe-bend
# rules/headless.rs `exit`). Grammar: crates/eukhe-bend/WIRE.md.
#
#   request  command failed, gave up (a Bool each); the run: 0 no run |
#            1 answered | 2 unanswered, then the reason; the primary
#            entry: 0 nothing | 1 answer | 2 unfinished | 3 provider
#            error | 4 aborted | 5 slash ok | 6 slash failed; compaction
#            failed, autonomous failed (a Bool each)
#   reason   0 model error | 1 run limit | 2 no model | 3 forced tool |
#            4 faulted | 5 aborted | 6 reset | 7 stale | 8 withdrawn |
#            9 other
#   reply    the code (Nat), then the cause: 0 answered | 1 command
#            failed | 2 gave up | 3 run failed, then the reason | 4
#            provider error | 5 aborted | 6 unfinished | 7 slash failed |
#            8 compaction failed | 9 autonomous failed
#
# Malformed input, or input left after the request, answers
# `E headless_exit: malformed request`, never a default.
# Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./headless_exit.bend as Hx

# Requests
# --------

def get_reason(r: W.Dec<Nat>) -> W.Dec<Hx.Reason>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          W.Got{Hx.ModelError{}, s}
        case 1n:
          W.Got{Hx.RunLimit{}, s}
        case 2n:
          W.Got{Hx.NoModel{}, s}
        case 3n:
          W.Got{Hx.ForcedTool{}, s}
        case 4n:
          W.Got{Hx.Faulted{}, s}
        case 5n:
          W.Got{Hx.Aborted{}, s}
        case 6n:
          W.Got{Hx.Reset{}, s}
        case 7n:
          W.Got{Hx.Stale{}, s}
        case 8n:
          W.Got{Hx.Withdrawn{}, s}
        case 9n:
          W.Got{Hx.Other{}, s}
        case 10n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_run.reason(d: W.Dec<Hx.Reason>) -> W.Dec<Hx.Run>:
  match d:
    case W.Got{x, s}:
      W.Got{Hx.Unanswered{x}, s}
    case W.Bad{}:
      W.Bad{}

def get_run(r: W.Dec<Nat>) -> W.Dec<Hx.Run>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          W.Got{Hx.NoRun{}, s}
        case 1n:
          W.Got{Hx.Answered{}, s}
        case 2n:
          get_run.reason(get_reason(W.get_nat(s)))
        case 3n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_primary(r: W.Dec<Nat>) -> W.Dec<Hx.Primary>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          W.Got{Hx.PNothing{}, s}
        case 1n:
          W.Got{Hx.PAnswer{}, s}
        case 2n:
          W.Got{Hx.PUnfinished{}, s}
        case 3n:
          W.Got{Hx.PProviderError{}, s}
        case 4n:
          W.Got{Hx.PAborted{}, s}
        case 5n:
          W.Got{Hx.PSlashOk{}, s}
        case 6n:
          W.Got{Hx.PSlashFailed{}, s}
        case 7n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_facts.auto(cf: Bool, gu: Bool, run: Hx.Run, p: Hx.Primary, c: Bool, d: W.Dec<Bool>) -> W.Dec<Hx.Facts>:
  match d:
    case W.Got{a, s}:
      W.Got{Hx.Facts{cf, gu, run, p, c, a}, s}
    case W.Bad{}:
      W.Bad{}

def get_facts.comp(cf: Bool, gu: Bool, run: Hx.Run, p: Hx.Primary, d: W.Dec<Bool>) -> W.Dec<Hx.Facts>:
  match d:
    case W.Got{c, s}:
      get_facts.auto(cf, gu, run, p, c, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_facts.primary(cf: Bool, gu: Bool, run: Hx.Run, d: W.Dec<Hx.Primary>) -> W.Dec<Hx.Facts>:
  match d:
    case W.Got{p, s}:
      get_facts.comp(cf, gu, run, p, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_facts.run(cf: Bool, gu: Bool, d: W.Dec<Hx.Run>) -> W.Dec<Hx.Facts>:
  match d:
    case W.Got{run, s}:
      get_facts.primary(cf, gu, run, get_primary(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_facts.gave_up(cf: Bool, d: W.Dec<Bool>) -> W.Dec<Hx.Facts>:
  match d:
    case W.Got{gu, s}:
      get_facts.run(cf, gu, get_run(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_facts.command(d: W.Dec<Bool>) -> W.Dec<Hx.Facts>:
  match d:
    case W.Got{cf, s}:
      get_facts.gave_up(cf, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

# the request at the start of s
def get_facts(s: String) -> W.Dec<Hx.Facts>:
  get_facts.command(W.get_bool(s))

# Replies
# -------

def put_reason(r: Hx.Reason, rest: String) -> String:
  match r:
    case Hx.ModelError{}:
      W.put_nat(0n, rest)
    case Hx.RunLimit{}:
      W.put_nat(1n, rest)
    case Hx.NoModel{}:
      W.put_nat(2n, rest)
    case Hx.ForcedTool{}:
      W.put_nat(3n, rest)
    case Hx.Faulted{}:
      W.put_nat(4n, rest)
    case Hx.Aborted{}:
      W.put_nat(5n, rest)
    case Hx.Reset{}:
      W.put_nat(6n, rest)
    case Hx.Stale{}:
      W.put_nat(7n, rest)
    case Hx.Withdrawn{}:
      W.put_nat(8n, rest)
    case Hx.Other{}:
      W.put_nat(9n, rest)

def put_cause(c: Hx.Cause, rest: String) -> String:
  match c:
    case Hx.CAnswered{}:
      W.put_nat(0n, rest)
    case Hx.CCommandFailed{}:
      W.put_nat(1n, rest)
    case Hx.CGaveUp{}:
      W.put_nat(2n, rest)
    case Hx.CRunFailed{r}:
      W.put_nat(3n, put_reason(r, rest))
    case Hx.CProviderError{}:
      W.put_nat(4n, rest)
    case Hx.CAborted{}:
      W.put_nat(5n, rest)
    case Hx.CUnfinished{}:
      W.put_nat(6n, rest)
    case Hx.CSlashFailed{}:
      W.put_nat(7n, rest)
    case Hx.CCompactionFailed{}:
      W.put_nat(8n, rest)
    case Hx.CAutonomousFailed{}:
      W.put_nat(9n, rest)

# the spelling of an exit: its code, then its cause
def put_verdict(v: Hx.Verdict, rest: String) -> String:
  match v:
    case Hx.Verdict{n, c}:
      W.put_nat(n, put_cause(c, rest))

def ffi.done(f: Hx.Facts, end: Bool) -> String:
  match end:
    case True{}:
      put_verdict(Hx.decide(f), "")
    case False{}:
      W.err("headless_exit: malformed request")

def ffi.got(r: W.Dec<Hx.Facts>) -> String:
  match r:
    case W.Got{f, +s}:
      ffi.done(f, W.end(s))
    case W.Bad{}:
      W.err("headless_exit: malformed request")

# the entry: decode the facts, answer the exit
def ffi(input: String) -> String:
  ffi.got(get_facts(input))
