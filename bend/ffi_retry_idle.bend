# ffi_retry_idle: the stepper of the compiled Bend core for the
# stream-idle deadline of one watched stream (bend/retry.bend section 6;
# crates/eukhe-ai/src/utils/stream_idle.rs `StreamIdle`): its state is the
# model's IdleSt, kept in the Bend heap. The codec is the wire format of
# bend/wire.bend (crates/eukhe-bend/WIRE.md):
#
#   open    the facts of stream_idle_timeout_ms (NaN: Bool, negative:
#           Bool, its whole part: Nat, a fraction: Bool), then the
#           deadline in us: Nat                     reply: Maybe<Wake>
#           (None: no deadline is armed; Some: the timer's first decision)
#   step    an event: 0, now (life) | 1 (a hold starts) | 2, now (a hold
#           ends) | 3, now (the timer fired)        reply: Maybe<Wake>
#           (None: nothing to do)
#   Wake    0 (the stream stalled) | 1, us (sleep us more from now)
#
# An open that arms nothing, or a malformed one, opens the shut state,
# which answers every step with the error form; a malformed event, or one
# with input left over, answers the error form and keeps the state.
# laws/retry_idle.bend pins the entry. Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./retry.bend as R

# The open
# --------

type Open is Data:
  Open{nan: Bool, neg: Bool, whole: Nat, frac: Bool, d: Nat}

def get_open.d(nan: Bool, neg: Bool, whole: Nat, frac: Bool, r: W.Dec<Nat>) -> W.Dec<Open>:
  match r:
    case W.Got{d, s}:
      W.Got{Open{nan, neg, whole, frac, d}, s}
    case W.Bad{}:
      W.Bad{}

def get_open.frac(nan: Bool, neg: Bool, whole: Nat, r: W.Dec<Bool>) -> W.Dec<Open>:
  match r:
    case W.Got{frac, s}:
      get_open.d(nan, neg, whole, frac, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_open.whole(nan: Bool, neg: Bool, r: W.Dec<Nat>) -> W.Dec<Open>:
  match r:
    case W.Got{whole, s}:
      get_open.frac(nan, neg, whole, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_open.neg(nan: Bool, r: W.Dec<Bool>) -> W.Dec<Open>:
  match r:
    case W.Got{neg, s}:
      get_open.whole(nan, neg, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_open.go(r: W.Dec<Bool>) -> W.Dec<Open>:
  match r:
    case W.Got{nan, s}:
      get_open.neg(nan, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

# the open at the start of s
def get_open(s: String) -> W.Dec<Open>:
  get_open.go(W.get_bool(s))

# The events
# ----------

def get_ev.life(r: W.Dec<Nat>) -> W.Dec<R.IdleEv>:
  match r:
    case W.Got{now, s}:
      W.Got{R.IdleLife{now}, s}
    case W.Bad{}:
      W.Bad{}

def get_ev.free(r: W.Dec<Nat>) -> W.Dec<R.IdleEv>:
  match r:
    case W.Got{now, s}:
      W.Got{R.IdleFree{now}, s}
    case W.Bad{}:
      W.Bad{}

def get_ev.fire(r: W.Dec<Nat>) -> W.Dec<R.IdleEv>:
  match r:
    case W.Got{now, s}:
      W.Got{R.IdleFire{now}, s}
    case W.Bad{}:
      W.Bad{}

def get_ev.tag(t: Nat, s: String) -> W.Dec<R.IdleEv>:
  match t:
    case 0n:
      get_ev.life(W.get_nat(s))
    case 1n:
      W.Got{R.IdleHold{}, s}
    case 2n:
      get_ev.free(W.get_nat(s))
    case 3n:
      get_ev.fire(W.get_nat(s))
    case 4n+p:
      W.Bad{}

def get_ev.go(r: W.Dec<Nat>) -> W.Dec<R.IdleEv>:
  match r:
    case W.Got{t, s}:
      get_ev.tag(t, s)
    case W.Bad{}:
      W.Bad{}

# the event at the start of s
def get_ev(s: String) -> W.Dec<R.IdleEv>:
  get_ev.go(W.get_nat(s))

# Replies
# -------

def put_wake(w: R.Wake) -> String:
  match w:
    case R.WakeStall{}:
      W.put_nat(0n, "")
    case R.WakeSleep{us}:
      W.put_nat(1n, W.put_nat(us, ""))

def put_reply(m: Maybe<&2, R.Wake>) -> String:
  match m:
    case None{}:
      W.put_nat(0n, "")
    case Some{w}:
      W.put_nat(1n, put_wake(w))

# The stepper
# -----------

# a watched stream's deadline, or none (unarmed or refused)
type St is Data:
  Live{s: R.IdleSt}
  Shut{}

def reply(r: R.IdleSt & Maybe<&2, R.Wake>) -> St & String:
  (s, m) = r
  (Live{s}, put_reply(m))

def open.armed(armed: Bool, +d: Nat) -> St & String:
  match armed:
    case True{}:
      reply(R.idle.open(d))
    case False{}:
      (Shut{}, put_reply(None{}))

def open.end(done: Bool, o: Open) -> St & String:
  match done:
    case True{}:
      match o:
        case Open{nan, neg, whole, frac, d}:
          open.armed(R.idle.arm(nan, neg, whole, frac), d)
    case False{}:
      (Shut{}, W.err("retry_idle: malformed open"))

def open.go(r: W.Dec<Open>) -> St & String:
  match r:
    case W.Got{o, s}:
      open.end(W.end(s), o)
    case W.Bad{}:
      (Shut{}, W.err("retry_idle: malformed open"))

# open: the deadline the facts arm, and its timer's first decision
def open(input: String) -> St & String:
  open.go(get_open(input))

def fail() -> String:
  W.err("retry_idle: malformed event")

def step.end(done: Bool, +s: R.IdleSt, e: R.IdleEv) -> St & String:
  match done:
    case True{}:
      reply(R.idle.step(s, e))
    case False{}:
      (Live{s}, fail())

def step.ev(s: R.IdleSt, r: W.Dec<R.IdleEv>) -> St & String:
  match r:
    case W.Got{e, rest}:
      step.end(W.end(rest), s, e)
    case W.Bad{}:
      (Live{s}, fail())

# step: one event of the stream's life; the reply is what the timer does
def step(st: St, input: String) -> St & String:
  match st:
    case Live{s}:
      step.ev(s, get_ev(input))
    case Shut{}:
      (Shut{}, W.err("retry_idle: no deadline"))
