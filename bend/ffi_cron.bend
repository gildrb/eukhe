import Base
import ./wire.bend as W
import ./cron.bend as Cr
import ./cron_store.bend as CS

# ffi_cron: the per-job decisions of the cron job store
# (bend/cron_store.bend `take`, `clear`, `recover`, `finish`, `cancel`,
# `resume`, on the clock unit CS.MINUTE: times in ms) as an entry of the
# compiled Bend core. A request is one job's facts:
#   status  0 active | 1 paused | 2 finished | 3 cancelled
#   plan    0 a one-shot | 1 an interval, then its ms | 2 a rule (a cron
#           expression; Rust evaluates it)
#   fact    a status, a plan, the next run (Maybe ms), the failures in a
#           row (a Nat)
# and a tag, then
#   0  a claim pass: a fact, whether a claim of it is on record (T|F), the
#      time it is due by, the clock (ms)
#   1  a claim's verdict: whose (0 this process's, then T|F it still runs
#      it here; 1 another's, then T|F that process is dead)
#   2  a recovery: a fact, whether a claim of it was cleared (T|F)
#   3  a finish step: a fact, whether it ran (T) or was skipped (F),
#      whether it failed (T|F), the clock
#   4  a cancel: a fact
#   5  a resume: a fact, the clock
# Reply (a next run: 0 none | 1 at, then the ms | 2 the rule's next match
# after the clock):
#   0  0 not due | 1 roll, then the next run | 2 claim, then the next run
#   1  T (clear the claim) | F (keep it)
#   2  0 kept | 1 interrupted, then a status and a next run (Maybe ms)
#   3  0 untouched | 1 ran | 2 skipped; ran and skipped then a status, a
#      next run and the failures in a row
#   4  0 already cancelled | 1 cut, then a status and a next run (Maybe ms)
#   5  0 resumed, then a status, a next run and the failures in a row |
#      1 ended (finished or cancelled) | 2 not recurring
# Any other input: the error form.

# Decoding
# --------

def get_status.tag(t: Nat, s: String) -> W.Dec<Cr.Status>:
  match t:
    case 0n:
      W.Got{Cr.Active{}, s}
    case 1n:
      W.Got{Cr.Paused{}, s}
    case 2n:
      W.Got{Cr.Finished{}, s}
    case 3n:
      W.Got{Cr.Cancelled{}, s}
    case 4n+p:
      W.Bad{}

def get_status(r: W.Dec<Nat>) -> W.Dec<Cr.Status>:
  match r:
    case W.Got{t, s}:
      get_status.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_plan.every(r: W.Dec<Nat>) -> W.Dec<CS.Plan>:
  match r:
    case W.Got{n, s}:
      W.Got{CS.PEvery{n}, s}
    case W.Bad{}:
      W.Bad{}

def get_plan.tag(t: Nat, s: String) -> W.Dec<CS.Plan>:
  match t:
    case 0n:
      W.Got{CS.POnce{}, s}
    case 1n:
      get_plan.every(W.get_nat(s))
    case 2n:
      W.Got{CS.PRule{}, s}
    case 3n+p:
      W.Bad{}

def get_plan(r: W.Dec<Nat>) -> W.Dec<CS.Plan>:
  match r:
    case W.Got{t, s}:
      get_plan.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_mnat.some(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, Nat>>:
  match r:
    case W.Got{n, s}:
      W.Got{Some{n}, s}
    case W.Bad{}:
      W.Bad{}

def get_mnat.tag(t: Nat, s: String) -> W.Dec<Maybe<&2, Nat>>:
  match t:
    case 0n:
      W.Got{None{}, s}
    case 1n:
      get_mnat.some(W.get_nat(s))
    case 2n+p:
      W.Bad{}

def get_mnat(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, Nat>>:
  match r:
    case W.Got{t, s}:
      get_mnat.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_fact.streak(st: Cr.Status, p: CS.Plan, m: Maybe<&2, Nat>, r: W.Dec<Nat>) -> W.Dec<CS.Fact>:
  match r:
    case W.Got{k, s}:
      W.Got{CS.Fact{st, p, m, k}, s}
    case W.Bad{}:
      W.Bad{}

def get_fact.next(st: Cr.Status, p: CS.Plan, r: W.Dec<Maybe<&2, Nat>>) -> W.Dec<CS.Fact>:
  match r:
    case W.Got{m, s}:
      get_fact.streak(st, p, m, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_fact.plan(st: Cr.Status, r: W.Dec<CS.Plan>) -> W.Dec<CS.Fact>:
  match r:
    case W.Got{p, s}:
      get_fact.next(st, p, get_mnat(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_fact.status(r: W.Dec<Cr.Status>) -> W.Dec<CS.Fact>:
  match r:
    case W.Got{st, s}:
      get_fact.plan(st, get_plan(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

# the fact at the start of s
def get_fact(s: String) -> W.Dec<CS.Fact>:
  get_fact.status(get_status(W.get_nat(s)))

def get_take.now(f: CS.Fact, c: Bool, d: Nat, r: W.Dec<Nat>) -> W.Dec<CS.Ask>:
  match r:
    case W.Got{n, s}:
      W.Got{CS.AskTake{f, c, d, n}, s}
    case W.Bad{}:
      W.Bad{}

def get_take.due(f: CS.Fact, c: Bool, r: W.Dec<Nat>) -> W.Dec<CS.Ask>:
  match r:
    case W.Got{d, s}:
      get_take.now(f, c, d, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_take.claimed(f: CS.Fact, r: W.Dec<Bool>) -> W.Dec<CS.Ask>:
  match r:
    case W.Got{c, s}:
      get_take.due(f, c, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_take(r: W.Dec<CS.Fact>) -> W.Dec<CS.Ask>:
  match r:
    case W.Got{f, s}:
      get_take.claimed(f, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_who.mine(r: W.Dec<Bool>) -> W.Dec<CS.Who>:
  match r:
    case W.Got{b, s}:
      W.Got{CS.Mine{b}, s}
    case W.Bad{}:
      W.Bad{}

def get_who.theirs(r: W.Dec<Bool>) -> W.Dec<CS.Who>:
  match r:
    case W.Got{b, s}:
      W.Got{CS.Theirs{b}, s}
    case W.Bad{}:
      W.Bad{}

def get_who.tag(t: Nat, s: String) -> W.Dec<CS.Who>:
  match t:
    case 0n:
      get_who.mine(W.get_bool(s))
    case 1n:
      get_who.theirs(W.get_bool(s))
    case 2n+p:
      W.Bad{}

def get_who(r: W.Dec<Nat>) -> W.Dec<CS.Who>:
  match r:
    case W.Got{t, s}:
      get_who.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_clear(r: W.Dec<CS.Who>) -> W.Dec<CS.Ask>:
  match r:
    case W.Got{w, s}:
      W.Got{CS.AskClear{w}, s}
    case W.Bad{}:
      W.Bad{}

def get_recover.cleared(f: CS.Fact, r: W.Dec<Bool>) -> W.Dec<CS.Ask>:
  match r:
    case W.Got{c, s}:
      W.Got{CS.AskRecover{f, c}, s}
    case W.Bad{}:
      W.Bad{}

def get_recover(r: W.Dec<CS.Fact>) -> W.Dec<CS.Ask>:
  match r:
    case W.Got{f, s}:
      get_recover.cleared(f, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_finish.now(f: CS.Fact, a: Bool, b: Bool, r: W.Dec<Nat>) -> W.Dec<CS.Ask>:
  match r:
    case W.Got{n, s}:
      W.Got{CS.AskFinish{f, a, b, n}, s}
    case W.Bad{}:
      W.Bad{}

def get_finish.failed(f: CS.Fact, a: Bool, r: W.Dec<Bool>) -> W.Dec<CS.Ask>:
  match r:
    case W.Got{b, s}:
      get_finish.now(f, a, b, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_finish.ran(f: CS.Fact, r: W.Dec<Bool>) -> W.Dec<CS.Ask>:
  match r:
    case W.Got{a, s}:
      get_finish.failed(f, a, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_finish(r: W.Dec<CS.Fact>) -> W.Dec<CS.Ask>:
  match r:
    case W.Got{f, s}:
      get_finish.ran(f, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_cancel(r: W.Dec<CS.Fact>) -> W.Dec<CS.Ask>:
  match r:
    case W.Got{f, s}:
      W.Got{CS.AskCancel{f}, s}
    case W.Bad{}:
      W.Bad{}

def get_resume.now(f: CS.Fact, r: W.Dec<Nat>) -> W.Dec<CS.Ask>:
  match r:
    case W.Got{n, s}:
      W.Got{CS.AskResume{f, n}, s}
    case W.Bad{}:
      W.Bad{}

def get_resume(r: W.Dec<CS.Fact>) -> W.Dec<CS.Ask>:
  match r:
    case W.Got{f, s}:
      get_resume.now(f, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_ask.tag(t: Nat, s: String) -> W.Dec<CS.Ask>:
  match t:
    case 0n:
      get_take(get_fact(s))
    case 1n:
      get_clear(get_who(W.get_nat(s)))
    case 2n:
      get_recover(get_fact(s))
    case 3n:
      get_finish(get_fact(s))
    case 4n:
      get_cancel(get_fact(s))
    case 5n:
      get_resume(get_fact(s))
    case 6n+p:
      W.Bad{}

def get_ask.go(r: W.Dec<Nat>) -> W.Dec<CS.Ask>:
  match r:
    case W.Got{t, s}:
      get_ask.tag(t, s)
    case W.Bad{}:
      W.Bad{}

# the request at the start of s
def get_ask(s: String) -> W.Dec<CS.Ask>:
  get_ask.go(W.get_nat(s))

# Encoding
# --------

def put_status(st: Cr.Status, rest: String) -> String:
  match st:
    case Cr.Active{}:
      W.put_nat(0n, rest)
    case Cr.Paused{}:
      W.put_nat(1n, rest)
    case Cr.Finished{}:
      W.put_nat(2n, rest)
    case Cr.Cancelled{}:
      W.put_nat(3n, rest)

def put_mnat(m: Maybe<&2, Nat>, rest: String) -> String:
  match m:
    case None{}:
      W.put_nat(0n, rest)
    case Some{n}:
      W.put_nat(1n, W.put_nat(n, rest))

def put_next(n: CS.Next, rest: String) -> String:
  match n:
    case CS.NNone{}:
      W.put_nat(0n, rest)
    case CS.NAt{x}:
      W.put_nat(1n, W.put_nat(x, rest))
    case CS.NRoll{}:
      W.put_nat(2n, rest)

def put_took(t: CS.Took, rest: String) -> String:
  match t:
    case CS.Keep{}:
      W.put_nat(0n, rest)
    case CS.Roll{n}:
      W.put_nat(1n, put_next(n, rest))
    case CS.Claimed{n}:
      W.put_nat(2n, put_next(n, rest))

def put_back(b: CS.Back, rest: String) -> String:
  match b:
    case CS.Kept{}:
      W.put_nat(0n, rest)
    case CS.Interrupted{st, m}:
      W.put_nat(1n, put_status(st, put_mnat(m, rest)))

def put_fin(x: CS.Fin, rest: String) -> String:
  match x:
    case CS.Untouched{}:
      W.put_nat(0n, rest)
    case CS.Ran{st, n, k}:
      W.put_nat(1n, put_status(st, put_next(n, W.put_nat(k, rest))))
    case CS.Skipped{st, n, k}:
      W.put_nat(2n, put_status(st, put_next(n, W.put_nat(k, rest))))

def put_cut(x: CS.Cut, rest: String) -> String:
  match x:
    case CS.Same{}:
      W.put_nat(0n, rest)
    case CS.Cut{st, m}:
      W.put_nat(1n, put_status(st, put_mnat(m, rest)))

def put_again(x: CS.Again, rest: String) -> String:
  match x:
    case CS.Resumed{st, n, k}:
      W.put_nat(0n, put_status(st, put_next(n, W.put_nat(k, rest))))
    case CS.Ended{}:
      W.put_nat(1n, rest)
    case CS.NotRecurring{}:
      W.put_nat(2n, rest)

# The entry
# ---------

# the answer to a request
def answer(a: CS.Ask) -> String:
  match a:
    case CS.AskTake{f, c, d, n}:
      put_took(CS.take(f, c, d, n), "")
    case CS.AskClear{w}:
      W.put_bool(CS.clear(w), "")
    case CS.AskRecover{f, c}:
      put_back(CS.recover(f, c), "")
    case CS.AskFinish{f, r, b, n}:
      put_fin(CS.finish(CS.MINUTE(), f, r, b, n), "")
    case CS.AskCancel{f}:
      put_cut(CS.cancel(f), "")
    case CS.AskResume{f, n}:
      put_again(CS.resume(f, n), "")

def fail() -> String:
  W.err("cron: malformed request")

def run.end(whole: Bool, a: CS.Ask) -> String:
  match whole:
    case True{}:
      answer(a)
    case False{}:
      fail()

def run(r: W.Dec<CS.Ask>) -> String:
  match r:
    case W.Got{a, s}:
      run.end(W.end(s), a)
    case W.Bad{}:
      fail()

def ffi(input: String) -> String:
  run(get_ask(input))
