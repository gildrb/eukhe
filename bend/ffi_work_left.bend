# ffi_work_left: the entry of the compiled Bend core that decides whether
# a run goes on past a final answer that leaves task work undone
# (bend/work_left.bend; Rust: eukhe-bend rules/work_left.rs `step`).
# Grammar: crates/eukhe-bend/WIRE.md.
#
#   request  four Bools: an autonomous run or a loop drives the run, input
#            is queued, the run acted, the budget admits more work; then
#            the progress check: 0 go | 1 stop, each with its count of
#            stalls (Nat), the Director loop's steps left (Nat), then the
#            judge's reading: 0 not read | 1 no work left | 2 work left |
#            3 no verdict
#   reply    0 continue, with the steps left after it (Nat) | 1 yield |
#            2 ask the judge
#
# Malformed input, or input left after the request, answers
# `E work_left: malformed request`, never a default.
# Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./progress.bend as Pg
import ./work_left.bend as Wl

# Requests
# --------

def get_stall.count(stop: Bool, r: W.Dec<Nat>) -> W.Dec<Pg.Goal>:
  match stop:
    case True{}:
      match r:
        case W.Got{k, s}:
          W.Got{Pg.Stop{k}, s}
        case W.Bad{}:
          W.Bad{}
    case False{}:
      match r:
        case W.Got{k, s}:
          W.Got{Pg.Go{k}, s}
        case W.Bad{}:
          W.Bad{}

def get_stall(r: W.Dec<Nat>) -> W.Dec<Pg.Goal>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          get_stall.count(False{}, W.get_nat(s))
        case 1n:
          get_stall.count(True{}, W.get_nat(s))
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

def get_facts.reading(d: Bool, q: Bool, a: Bool, b: Bool, s: Pg.Goal, n: Nat, x: W.Dec<Wl.Reading>) -> W.Dec<Wl.Facts>:
  match x:
    case W.Got{r, t}:
      W.Got{Wl.Facts{d, q, a, b, s, n, r}, t}
    case W.Bad{}:
      W.Bad{}

def get_facts.left(d: Bool, q: Bool, a: Bool, b: Bool, s: Pg.Goal, x: W.Dec<Nat>) -> W.Dec<Wl.Facts>:
  match x:
    case W.Got{n, t}:
      get_facts.reading(d, q, a, b, s, n, get_reading(W.get_nat(t)))
    case W.Bad{}:
      W.Bad{}

def get_facts.stall(d: Bool, q: Bool, a: Bool, b: Bool, x: W.Dec<Pg.Goal>) -> W.Dec<Wl.Facts>:
  match x:
    case W.Got{s, t}:
      get_facts.left(d, q, a, b, s, W.get_nat(t))
    case W.Bad{}:
      W.Bad{}

def get_facts.funded(d: Bool, q: Bool, a: Bool, x: W.Dec<Bool>) -> W.Dec<Wl.Facts>:
  match x:
    case W.Got{b, t}:
      get_facts.stall(d, q, a, b, get_stall(W.get_nat(t)))
    case W.Bad{}:
      W.Bad{}

def get_facts.acted(d: Bool, q: Bool, x: W.Dec<Bool>) -> W.Dec<Wl.Facts>:
  match x:
    case W.Got{a, t}:
      get_facts.funded(d, q, a, W.get_bool(t))
    case W.Bad{}:
      W.Bad{}

def get_facts.queued(d: Bool, x: W.Dec<Bool>) -> W.Dec<Wl.Facts>:
  match x:
    case W.Got{q, t}:
      get_facts.acted(d, q, W.get_bool(t))
    case W.Bad{}:
      W.Bad{}

def get_facts.driven(x: W.Dec<Bool>) -> W.Dec<Wl.Facts>:
  match x:
    case W.Got{d, t}:
      get_facts.queued(d, W.get_bool(t))
    case W.Bad{}:
      W.Bad{}

# the request at the start of s
def get_facts(s: String) -> W.Dec<Wl.Facts>:
  get_facts.driven(W.get_bool(s))

# Replies
# -------

# the spelling of a step
def put_step(s: Wl.Step, rest: String) -> String:
  match s:
    case Wl.Continue{m}:
      W.put_nat(0n, W.put_nat(m, rest))
    case Wl.Yield{}:
      W.put_nat(1n, rest)
    case Wl.Ask{}:
      W.put_nat(2n, rest)

def ffi.done(f: Wl.Facts, end: Bool) -> String:
  match end:
    case True{}:
      put_step(Wl.decide(f), "")
    case False{}:
      W.err("work_left: malformed request")

def ffi.got(r: W.Dec<Wl.Facts>) -> String:
  match r:
    case W.Got{f, +s}:
      ffi.done(f, W.end(s))
    case W.Bad{}:
      W.err("work_left: malformed request")

# the entry: decode the facts, answer the step
def ffi(input: String) -> String:
  ffi.got(get_facts(input))
