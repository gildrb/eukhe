# ffi_revive: the compiled Bend core's entry for the boot revival's veto
# (bend/revive.bend `veto`). Rust `revival_gate::revival_veto` gathers the
# facts and calls it through `eukhe_bend::call`.
#
# Request (crates/eukhe-bend/WIRE.md): a record
#   failed: Bool         the supervisor gave the worker up
#   archived: Bool       its session file holds the archived belt
#   lease: Maybe<Nat>    the pid of a live worker holding its session lease
#   busy: tag            0 no busy record with a stamp, 1 a stamp that
#                        cannot be read, 2 recorded at `at: Nat` (ms)
#   now, max, skew: Nat  the boot's time, the max age, the skew (ms)
# Reply: a tag: 0 revive, 1 gave up, 2 archived, 3 leased (then the pid),
# 4 no busy evidence, 5 stale busy evidence. A malformed request or input
# left over answers the error form "revive: malformed request".

import Base
import ./wire.bend as W
import ./revive.bend as M

# Decoding
# --------

def get_facts.skew(f: Bool, a: Bool, l: Maybe<&2, Nat>, b: M.Busy, n: Nat, m: Nat, r: W.Dec<Nat>) -> W.Dec<M.Facts>:
  match r:
    case W.Got{k, rest}:
      W.Got{M.Facts{f, a, l, b, n, m, k}, rest}
    case W.Bad{}:
      W.Bad{}

def get_facts.max(f: Bool, a: Bool, l: Maybe<&2, Nat>, b: M.Busy, n: Nat, r: W.Dec<Nat>) -> W.Dec<M.Facts>:
  match r:
    case W.Got{m, rest}:
      get_facts.skew(f, a, l, b, n, m, W.get_nat(rest))
    case W.Bad{}:
      W.Bad{}

def get_facts.now.n(f: Bool, a: Bool, l: Maybe<&2, Nat>, b: M.Busy, r: W.Dec<Nat>) -> W.Dec<M.Facts>:
  match r:
    case W.Got{n, rest}:
      get_facts.max(f, a, l, b, n, W.get_nat(rest))
    case W.Bad{}:
      W.Bad{}

def get_facts.now(f: Bool, a: Bool, l: Maybe<&2, Nat>, r: W.Dec<M.Busy>) -> W.Dec<M.Facts>:
  match r:
    case W.Got{b, rest}:
      get_facts.now.n(f, a, l, b, W.get_nat(rest))
    case W.Bad{}:
      W.Bad{}

def get_busy.at(r: W.Dec<Nat>) -> W.Dec<M.Busy>:
  match r:
    case W.Got{at, rest}:
      W.Got{M.Stamp{at}, rest}
    case W.Bad{}:
      W.Bad{}

def get_busy.tag(t: Nat, s: String) -> W.Dec<M.Busy>:
  match t:
    case 0n:
      W.Got{M.NoBusy{}, s}
    case 1n:
      W.Got{M.Unread{}, s}
    case 2n:
      get_busy.at(W.get_nat(s))
    case 3n+p:
      W.Bad{}

def get_busy(r: W.Dec<Nat>) -> W.Dec<M.Busy>:
  match r:
    case W.Got{t, s}:
      get_busy.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_facts.busy(f: Bool, a: Bool, r: W.Dec<Maybe<&2, Nat>>) -> W.Dec<M.Facts>:
  match r:
    case W.Got{l, rest}:
      get_facts.now(f, a, l, get_busy(W.get_nat(rest)))
    case W.Bad{}:
      W.Bad{}

def get_lease.pid(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, Nat>>:
  match r:
    case W.Got{p, rest}:
      W.Got{Some{p}, rest}
    case W.Bad{}:
      W.Bad{}

def get_lease.tag(t: Nat, s: String) -> W.Dec<Maybe<&2, Nat>>:
  match t:
    case 0n:
      W.Got{None{}, s}
    case 1n:
      get_lease.pid(W.get_nat(s))
    case 2n+p:
      W.Bad{}

def get_lease(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, Nat>>:
  match r:
    case W.Got{t, s}:
      get_lease.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_facts.lease(f: Bool, r: W.Dec<Bool>) -> W.Dec<M.Facts>:
  match r:
    case W.Got{a, rest}:
      get_facts.busy(f, a, get_lease(W.get_nat(rest)))
    case W.Bad{}:
      W.Bad{}

def get_facts.archived(r: W.Dec<Bool>) -> W.Dec<M.Facts>:
  match r:
    case W.Got{f, rest}:
      get_facts.lease(f, W.get_bool(rest))
    case W.Bad{}:
      W.Bad{}

# the facts at the start of s
def get_facts(s: String) -> W.Dec<M.Facts>:
  get_facts.archived(W.get_bool(s))

# Encoding
# --------

def put_veto(v: M.Veto) -> String:
  match v:
    case M.Revive{}:
      W.put_nat(0n, "")
    case M.GaveUp{}:
      W.put_nat(1n, "")
    case M.Archived{}:
      W.put_nat(2n, "")
    case M.Leased{p}:
      W.put_nat(3n, W.put_nat(p, ""))
    case M.NoEvidence{}:
      W.put_nat(4n, "")
    case M.Stale{}:
      W.put_nat(5n, "")

# The entry
# ---------

def ffi.fin(done: Bool, f: M.Facts) -> String:
  match done:
    case True{}:
      put_veto(M.veto(f))
    case False{}:
      W.err("revive: malformed request")

def ffi.go(r: W.Dec<M.Facts>) -> String:
  match r:
    case W.Got{f, rest}:
      ffi.fin(W.end(rest), f)
    case W.Bad{}:
      W.err("revive: malformed request")

def ffi(input: String) -> String:
  ffi.go(get_facts(input))
