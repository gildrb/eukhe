# ffi_retry_idle: the stream-idle deadline's decisions of the compiled Bend
# core (bend/retry.bend section 6) behind one entry, `ffi`. A request names
# its decision and carries its input (crates/eukhe-bend/WIRE.md is the
# grammar):
#
#   tag 0  arm    the facts of stream_idle_timeout_ms: NaN, negative,
#                 its whole part, a fraction      -> Bool (armed)
#   tag 1  wake   the clock held, the time since the stream last
#                 showed life, the deadline        -> a Wake
#
# A Wake is WakeStall (tag 0) or WakeSleep (tag 1, then the time to sleep).
# Malformed input, and input left after the request, answer the error
# form, never a default. laws/retry_idle.bend states the laws of this
# entry; PROOF.bend proves them. Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./retry.bend as R

# A request of the entry
type Req is Data:
  QArm{nan: Bool, neg: Bool, whole: Nat, frac: Bool}
  QWake{held: Bool, since: Nat, d: Nat}

# Decoding
# --------

def get_arm.frac(nan: Bool, neg: Bool, whole: Nat, r: W.Dec<Bool>) -> W.Dec<Req>:
  match r:
    case W.Got{frac, s}:
      W.Got{QArm{nan, neg, whole, frac}, s}
    case W.Bad{}:
      W.Bad{}

def get_arm.whole(nan: Bool, neg: Bool, r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{whole, s}:
      get_arm.frac(nan, neg, whole, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_arm.neg(nan: Bool, r: W.Dec<Bool>) -> W.Dec<Req>:
  match r:
    case W.Got{neg, s}:
      get_arm.whole(nan, neg, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_arm(r: W.Dec<Bool>) -> W.Dec<Req>:
  match r:
    case W.Got{nan, s}:
      get_arm.neg(nan, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_wake.d(held: Bool, since: Nat, r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{d, s}:
      W.Got{QWake{held, since, d}, s}
    case W.Bad{}:
      W.Bad{}

def get_wake.since(held: Bool, r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{since, s}:
      get_wake.d(held, since, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_wake(r: W.Dec<Bool>) -> W.Dec<Req>:
  match r:
    case W.Got{held, s}:
      get_wake.since(held, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_req.tag(t: Nat, s: String) -> W.Dec<Req>:
  match t:
    case 0n:
      get_arm(W.get_bool(s))
    case 1n:
      get_wake(W.get_bool(s))
    case 2n+u:
      W.Bad{}

def get_req.go(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{t, s}:
      get_req.tag(t, s)
    case W.Bad{}:
      W.Bad{}

# the request at the start of s
def get_req(s: String) -> W.Dec<Req>:
  get_req.go(W.get_nat(s))

# Replies
# -------

def put_wake(w: R.Wake) -> String:
  match w:
    case R.WakeStall{}:
      W.put_nat(0n, "")
    case R.WakeSleep{us}:
      W.put_nat(1n, W.put_nat(us, ""))

# the reply of a request: the model's decision, encoded
def answer(q: Req) -> String:
  match q:
    case QArm{nan, neg, whole, frac}:
      W.put_bool(R.idle.arm(nan, neg, whole, frac), "")
    case QWake{held, since, d}:
      put_wake(R.idle.wake(held, since, d))

def fail() -> String:
  W.err("retry_idle: malformed request")

def run.end(whole: Bool, q: Req) -> String:
  match whole:
    case True{}:
      answer(q)
    case False{}:
      fail()

def run(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, s}:
      run.end(W.end(s), q)
    case W.Bad{}:
      fail()

# the entry: decode the request, answer the model's decision
def ffi(input: String) -> String:
  run(get_req(input))
