# ffi_headless_settle: the entry of the compiled Bend core that decides
# whether a headless run may stop waiting (bend/headless_settle.bend;
# Rust: eukhe-bend rules/headless.rs `settle`). Grammar:
# crates/eukhe-bend/WIRE.md.
#
#   request  busy (Bool), jobs, kernel jobs, children, workflow runs,
#            wakes (a Nat each), unknown, limit hit (a Bool each)
#   reply    0 finished | 1 waiting | 2 give up
#
# Malformed input, or input left after the request, answers
# `E headless_settle: malformed request`, never a default.
# Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./headless_settle.bend as Hs

# Requests
# --------

def get_facts.limit(b: Bool, j: Nat, k: Nat, c: Nat, w: Nat, x: Nat, u: Bool, d: W.Dec<Bool>) -> W.Dec<Hs.Facts>:
  match d:
    case W.Got{l, s}:
      W.Got{Hs.Facts{b, j, k, c, w, x, u, l}, s}
    case W.Bad{}:
      W.Bad{}

def get_facts.unknown(b: Bool, j: Nat, k: Nat, c: Nat, w: Nat, x: Nat, d: W.Dec<Bool>) -> W.Dec<Hs.Facts>:
  match d:
    case W.Got{u, s}:
      get_facts.limit(b, j, k, c, w, x, u, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_facts.wakes(b: Bool, j: Nat, k: Nat, c: Nat, w: Nat, d: W.Dec<Nat>) -> W.Dec<Hs.Facts>:
  match d:
    case W.Got{x, s}:
      get_facts.unknown(b, j, k, c, w, x, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_facts.runs(b: Bool, j: Nat, k: Nat, c: Nat, d: W.Dec<Nat>) -> W.Dec<Hs.Facts>:
  match d:
    case W.Got{w, s}:
      get_facts.wakes(b, j, k, c, w, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_facts.children(b: Bool, j: Nat, k: Nat, d: W.Dec<Nat>) -> W.Dec<Hs.Facts>:
  match d:
    case W.Got{c, s}:
      get_facts.runs(b, j, k, c, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_facts.kernel(b: Bool, j: Nat, d: W.Dec<Nat>) -> W.Dec<Hs.Facts>:
  match d:
    case W.Got{k, s}:
      get_facts.children(b, j, k, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_facts.jobs(b: Bool, d: W.Dec<Nat>) -> W.Dec<Hs.Facts>:
  match d:
    case W.Got{j, s}:
      get_facts.kernel(b, j, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_facts.busy(d: W.Dec<Bool>) -> W.Dec<Hs.Facts>:
  match d:
    case W.Got{b, s}:
      get_facts.jobs(b, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

# the request at the start of s
def get_facts(s: String) -> W.Dec<Hs.Facts>:
  get_facts.busy(W.get_bool(s))

# Replies
# -------

# the spelling of a decision, then rest
def put_settle(x: Hs.Settle, rest: String) -> String:
  match x:
    case Hs.Finished{}:
      W.put_nat(0n, rest)
    case Hs.Waiting{}:
      W.put_nat(1n, rest)
    case Hs.GiveUp{}:
      W.put_nat(2n, rest)

def ffi.done(f: Hs.Facts, end: Bool) -> String:
  match end:
    case True{}:
      put_settle(Hs.settle(f), "")
    case False{}:
      W.err("headless_settle: malformed request")

def ffi.got(r: W.Dec<Hs.Facts>) -> String:
  match r:
    case W.Got{f, +s}:
      ffi.done(f, W.end(s))
    case W.Bad{}:
      W.err("headless_settle: malformed request")

# the entry: decode the facts, answer the decision
def ffi(input: String) -> String:
  ffi.got(get_facts(input))
