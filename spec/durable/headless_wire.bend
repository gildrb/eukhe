# durable (spec): the wire of the headless_settle and headless_exit
# entries (bend/ffi_headless_settle.bend, bend/ffi_headless_exit.bend,
# crates/eukhe-bend/WIRE.md) restated without the entries' code: how Rust
# spells a request, which requests fit the wire, how a decision is spelled
# as a reply, and the reader of a request. The laws of areas
# headless_settle and headless_exit state that the entries answer the
# spelled decision of the core. A spec: the shipped code never calls it.
#
# W1: a settle request is busy (Bool), then jobs, kernel jobs, children,
#     workflow runs and wakes (a Nat each), then unknown and limit hit
#     (a Bool each); it fits when each count fits the wire.
# W2: a settle reply is 0 finished, 1 waiting or 2 give up.
# W3: an exit request is command failed (a Bool), the wait (0 quiet | 1
#     gave up | 2 budget deadline, in the order of bend/headless_exit.bend
#     Wait), the run (0 no run | 1 answered | 2 unanswered, then its
#     reason: 0 model error .. 10 budget refused, in the order of Reason),
#     the primary entry (0 nothing .. 7 budget refused, in the order of
#     Primary), then compaction failed, autonomous failed and budget
#     answered (a Bool each).
# W4: an exit reply is the code (Nat), then the cause (0 answered ..
#     11 budget unanswered, in the order of Cause; 3 run failed is
#     followed by its reason).
# W5: anything else is no request.

import Base
import ../../bend/headless_settle.bend as Hs
import ../../bend/headless_exit.bend as Hx
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase

# Settle requests and replies (W1-W2)
# -----------------------------------

# a settle request, then rest
def w_settle_req(f: Hs.Facts, rest: String) -> String:
  match f:
    case Hs.Facts{b, j, k, c, w, x, u, l}:
      Wr.put_bool(b, Wr.put_nat(j, Wr.put_nat(k, Wr.put_nat(c, Wr.put_nat(w, Wr.put_nat(x, Wr.put_bool(u, Wr.put_bool(l, rest))))))))

# every count of a settle request fits the wire
def fit_settle(f: Hs.Facts) -> Bool:
  match f:
    case Hs.Facts{b, j, k, c, w, x, u, l}:
      Bool.and(LawsBase.wire_fits(j), Bool.and(LawsBase.wire_fits(k), Bool.and(LawsBase.wire_fits(c), Bool.and(LawsBase.wire_fits(w), LawsBase.wire_fits(x)))))

def w_settle(x: Hs.Settle, rest: String) -> String:
  match x:
    case Hs.Finished{}:
      Wr.put_nat(0n, rest)
    case Hs.Waiting{}:
      Wr.put_nat(1n, rest)
    case Hs.GiveUp{}:
      Wr.put_nat(2n, rest)

# The settle reader (W5)
# ----------------------

def r_settle.limit(b: Bool, j: Nat, k: Nat, c: Nat, w: Nat, x: Nat, u: Bool, d: Wr.Dec<Bool>) -> Wr.Dec<Hs.Facts>:
  match d:
    case Wr.Got{l, s}:
      Wr.Got{Hs.Facts{b, j, k, c, w, x, u, l}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def r_settle.unknown(b: Bool, j: Nat, k: Nat, c: Nat, w: Nat, x: Nat, d: Wr.Dec<Bool>) -> Wr.Dec<Hs.Facts>:
  match d:
    case Wr.Got{u, s}:
      r_settle.limit(b, j, k, c, w, x, u, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def r_settle.wakes(b: Bool, j: Nat, k: Nat, c: Nat, w: Nat, d: Wr.Dec<Nat>) -> Wr.Dec<Hs.Facts>:
  match d:
    case Wr.Got{x, s}:
      r_settle.unknown(b, j, k, c, w, x, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def r_settle.runs(b: Bool, j: Nat, k: Nat, c: Nat, d: Wr.Dec<Nat>) -> Wr.Dec<Hs.Facts>:
  match d:
    case Wr.Got{w, s}:
      r_settle.wakes(b, j, k, c, w, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def r_settle.children(b: Bool, j: Nat, k: Nat, d: Wr.Dec<Nat>) -> Wr.Dec<Hs.Facts>:
  match d:
    case Wr.Got{c, s}:
      r_settle.runs(b, j, k, c, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def r_settle.kernel(b: Bool, j: Nat, d: Wr.Dec<Nat>) -> Wr.Dec<Hs.Facts>:
  match d:
    case Wr.Got{k, s}:
      r_settle.children(b, j, k, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def r_settle.jobs(b: Bool, d: Wr.Dec<Nat>) -> Wr.Dec<Hs.Facts>:
  match d:
    case Wr.Got{j, s}:
      r_settle.kernel(b, j, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def r_settle.busy(d: Wr.Dec<Bool>) -> Wr.Dec<Hs.Facts>:
  match d:
    case Wr.Got{b, s}:
      r_settle.jobs(b, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

# a settle request at the start of s, read with the wire's decoders
def r_settle(s: String) -> Wr.Dec<Hs.Facts>:
  r_settle.busy(Wr.get_bool(s))

def r_settle_whole.end(e: Bool, f: Hs.Facts) -> Maybe<&2, Hs.Facts>:
  match e:
    case True{}:
      Some{f}
    case False{}:
      None{}

def r_settle_whole(d: Wr.Dec<Hs.Facts>) -> Maybe<&2, Hs.Facts>:
  match d:
    case Wr.Got{f, +s}:
      r_settle_whole.end(Wr.end(s), f)
    case Wr.Bad{}:
      None{}

# the settle request s spells whole, with nothing after it
def read_settle(s: String) -> Maybe<&2, Hs.Facts>:
  r_settle_whole(r_settle(s))

# Exit requests and replies (W3-W4)
# ---------------------------------

def w_reason(r: Hx.Reason, rest: String) -> String:
  match r:
    case Hx.ModelError{}:
      Wr.put_nat(0n, rest)
    case Hx.RunLimit{}:
      Wr.put_nat(1n, rest)
    case Hx.NoModel{}:
      Wr.put_nat(2n, rest)
    case Hx.ForcedTool{}:
      Wr.put_nat(3n, rest)
    case Hx.Faulted{}:
      Wr.put_nat(4n, rest)
    case Hx.Aborted{}:
      Wr.put_nat(5n, rest)
    case Hx.Reset{}:
      Wr.put_nat(6n, rest)
    case Hx.Stale{}:
      Wr.put_nat(7n, rest)
    case Hx.Withdrawn{}:
      Wr.put_nat(8n, rest)
    case Hx.Other{}:
      Wr.put_nat(9n, rest)
    case Hx.BudgetRefused{}:
      Wr.put_nat(10n, rest)

def w_wait(w: Hx.Wait, rest: String) -> String:
  match w:
    case Hx.Quiet{}:
      Wr.put_nat(0n, rest)
    case Hx.GaveUp{}:
      Wr.put_nat(1n, rest)
    case Hx.BudgetDeadline{}:
      Wr.put_nat(2n, rest)

def w_run(run: Hx.Run, rest: String) -> String:
  match run:
    case Hx.NoRun{}:
      Wr.put_nat(0n, rest)
    case Hx.Answered{}:
      Wr.put_nat(1n, rest)
    case Hx.Unanswered{r}:
      Wr.put_nat(2n, w_reason(r, rest))

def w_primary(p: Hx.Primary, rest: String) -> String:
  match p:
    case Hx.PNothing{}:
      Wr.put_nat(0n, rest)
    case Hx.PAnswer{}:
      Wr.put_nat(1n, rest)
    case Hx.PUnfinished{}:
      Wr.put_nat(2n, rest)
    case Hx.PProviderError{}:
      Wr.put_nat(3n, rest)
    case Hx.PAborted{}:
      Wr.put_nat(4n, rest)
    case Hx.PSlashOk{}:
      Wr.put_nat(5n, rest)
    case Hx.PSlashFailed{}:
      Wr.put_nat(6n, rest)
    case Hx.PBudgetRefused{}:
      Wr.put_nat(7n, rest)

# an exit request, then rest
def w_exit_req(f: Hx.Facts, rest: String) -> String:
  match f:
    case Hx.Facts{cf, w, run, p, c, a, ba}:
      Wr.put_bool(cf, w_wait(w, w_run(run, w_primary(p, Wr.put_bool(c, Wr.put_bool(a, Wr.put_bool(ba, rest)))))))

def w_cause(c: Hx.Cause, rest: String) -> String:
  match c:
    case Hx.CAnswered{}:
      Wr.put_nat(0n, rest)
    case Hx.CCommandFailed{}:
      Wr.put_nat(1n, rest)
    case Hx.CGaveUp{}:
      Wr.put_nat(2n, rest)
    case Hx.CRunFailed{r}:
      Wr.put_nat(3n, w_reason(r, rest))
    case Hx.CProviderError{}:
      Wr.put_nat(4n, rest)
    case Hx.CAborted{}:
      Wr.put_nat(5n, rest)
    case Hx.CUnfinished{}:
      Wr.put_nat(6n, rest)
    case Hx.CSlashFailed{}:
      Wr.put_nat(7n, rest)
    case Hx.CCompactionFailed{}:
      Wr.put_nat(8n, rest)
    case Hx.CAutonomousFailed{}:
      Wr.put_nat(9n, rest)
    case Hx.CBudgetLimited{}:
      Wr.put_nat(10n, rest)
    case Hx.CBudgetUnanswered{}:
      Wr.put_nat(11n, rest)

def w_verdict(v: Hx.Verdict, rest: String) -> String:
  match v:
    case Hx.Verdict{n, c}:
      Wr.put_nat(n, w_cause(c, rest))

# The exit reader (W5)
# --------------------

def r_wait(d: Wr.Dec<Nat>) -> Wr.Dec<Hx.Wait>:
  match d:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          Wr.Got{Hx.Quiet{}, s}
        case 1n:
          Wr.Got{Hx.GaveUp{}, s}
        case 2n:
          Wr.Got{Hx.BudgetDeadline{}, s}
        case 3n+u:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

def r_reason(d: Wr.Dec<Nat>) -> Wr.Dec<Hx.Reason>:
  match d:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          Wr.Got{Hx.ModelError{}, s}
        case 1n:
          Wr.Got{Hx.RunLimit{}, s}
        case 2n:
          Wr.Got{Hx.NoModel{}, s}
        case 3n:
          Wr.Got{Hx.ForcedTool{}, s}
        case 4n:
          Wr.Got{Hx.Faulted{}, s}
        case 5n:
          Wr.Got{Hx.Aborted{}, s}
        case 6n:
          Wr.Got{Hx.Reset{}, s}
        case 7n:
          Wr.Got{Hx.Stale{}, s}
        case 8n:
          Wr.Got{Hx.Withdrawn{}, s}
        case 9n:
          Wr.Got{Hx.Other{}, s}
        case 10n:
          Wr.Got{Hx.BudgetRefused{}, s}
        case 11n+u:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

def r_run.reason(d: Wr.Dec<Hx.Reason>) -> Wr.Dec<Hx.Run>:
  match d:
    case Wr.Got{r, s}:
      Wr.Got{Hx.Unanswered{r}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def r_run(d: Wr.Dec<Nat>) -> Wr.Dec<Hx.Run>:
  match d:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          Wr.Got{Hx.NoRun{}, s}
        case 1n:
          Wr.Got{Hx.Answered{}, s}
        case 2n:
          r_run.reason(r_reason(Wr.get_nat(s)))
        case 3n+u:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

def r_primary(d: Wr.Dec<Nat>) -> Wr.Dec<Hx.Primary>:
  match d:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          Wr.Got{Hx.PNothing{}, s}
        case 1n:
          Wr.Got{Hx.PAnswer{}, s}
        case 2n:
          Wr.Got{Hx.PUnfinished{}, s}
        case 3n:
          Wr.Got{Hx.PProviderError{}, s}
        case 4n:
          Wr.Got{Hx.PAborted{}, s}
        case 5n:
          Wr.Got{Hx.PSlashOk{}, s}
        case 6n:
          Wr.Got{Hx.PSlashFailed{}, s}
        case 7n:
          Wr.Got{Hx.PBudgetRefused{}, s}
        case 8n+u:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

def r_exit.budget(cf: Bool, w: Hx.Wait, run: Hx.Run, p: Hx.Primary, c: Bool, a: Bool, d: Wr.Dec<Bool>) -> Wr.Dec<Hx.Facts>:
  match d:
    case Wr.Got{ba, s}:
      Wr.Got{Hx.Facts{cf, w, run, p, c, a, ba}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def r_exit.auto(cf: Bool, w: Hx.Wait, run: Hx.Run, p: Hx.Primary, c: Bool, d: Wr.Dec<Bool>) -> Wr.Dec<Hx.Facts>:
  match d:
    case Wr.Got{a, s}:
      r_exit.budget(cf, w, run, p, c, a, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def r_exit.comp(cf: Bool, w: Hx.Wait, run: Hx.Run, p: Hx.Primary, d: Wr.Dec<Bool>) -> Wr.Dec<Hx.Facts>:
  match d:
    case Wr.Got{c, s}:
      r_exit.auto(cf, w, run, p, c, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def r_exit.primary(cf: Bool, w: Hx.Wait, run: Hx.Run, d: Wr.Dec<Hx.Primary>) -> Wr.Dec<Hx.Facts>:
  match d:
    case Wr.Got{p, s}:
      r_exit.comp(cf, w, run, p, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def r_exit.run(cf: Bool, w: Hx.Wait, d: Wr.Dec<Hx.Run>) -> Wr.Dec<Hx.Facts>:
  match d:
    case Wr.Got{run, s}:
      r_exit.primary(cf, w, run, r_primary(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def r_exit.wait(cf: Bool, d: Wr.Dec<Hx.Wait>) -> Wr.Dec<Hx.Facts>:
  match d:
    case Wr.Got{w, s}:
      r_exit.run(cf, w, r_run(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def r_exit.command(d: Wr.Dec<Bool>) -> Wr.Dec<Hx.Facts>:
  match d:
    case Wr.Got{cf, s}:
      r_exit.wait(cf, r_wait(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

# an exit request at the start of s, read with the wire's decoders
def r_exit(s: String) -> Wr.Dec<Hx.Facts>:
  r_exit.command(Wr.get_bool(s))

def r_exit_whole.end(e: Bool, f: Hx.Facts) -> Maybe<&2, Hx.Facts>:
  match e:
    case True{}:
      Some{f}
    case False{}:
      None{}

def r_exit_whole(d: Wr.Dec<Hx.Facts>) -> Maybe<&2, Hx.Facts>:
  match d:
    case Wr.Got{f, +s}:
      r_exit_whole.end(Wr.end(s), f)
    case Wr.Bad{}:
      None{}

# the exit request s spells whole, with nothing after it
def read_exit(s: String) -> Maybe<&2, Hx.Facts>:
  r_exit_whole(r_exit(s))
