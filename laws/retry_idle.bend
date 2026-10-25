# eukhe: the laws of area retry_idle

import Base
import ../bend/ffi_retry_idle.bend as Fi
import ../bend/retry.bend as R
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# ---- retry_idle ----

# LAWS (RI, the stream-idle deadline): when a provider stream that shows
# no life stalls (crates/eukhe-ai/src/utils/stream_idle.rs). Whether a
# deadline is armed and what its timer decides when it fires run as the
# model of bend/retry.bend (section 6), compiled behind
# bend/ffi_retry_idle.bend; Rust (`StreamIdle`) only stores the time of the
# stream's last event (`touch`, no core call), counts the holds, sleeps as
# the core says and aborts on a stall. PROOF.bend proves these laws (as
# RetryIdle.<law>) with the lemmas of proof/retry_idle/. The race of an
# event and the timer at the same instant is tokio's: the bridge test
# crates/eukhe-durable/src/harness/generation/retry_bridge.rs runs the real
# loop on paused time against R.idle (bridge/bridge_retry.bend).

# Terms
# -----

def wake_spec.free(early: Bool, left: Nat) -> R.Wake:
  match early:
    case True{}:
      R.WakeSleep{left}
    case False{}:
      R.WakeStall{}

# what the timer decides when it fires `since` after the last life of a
# stream under a deadline of d: a held clock sleeps a whole deadline; a
# free one sleeps what is left of d, and stalls once d has passed
def wake_spec(held: Bool, +since: Nat, +d: Nat) -> R.Wake:
  match held:
    case True{}:
      R.WakeSleep{d}
    case False{}:
      wake_spec.free(Nat.is_lt(since, d), Nat.sub(d, since))

# a timeout is armed when it is a number above 0: not NaN, not negative,
# and a whole part or a fraction above 0
def arm_spec(nan: Bool, neg: Bool, whole: Nat, frac: Bool) -> Bool:
  match nan:
    case True{}:
      False{}
    case False{}:
      match neg:
        case True{}:
          False{}
        case False{}:
          match whole:
            case 0n:
              frac
            case 1n+p:
              True{}

# The timer loop
# --------------
# The loop of `StreamIdle::within`, driven by the model's wake decision
# alone: the timer fires `k` after the stream's last event (at `last`);
# an event that comes at or before the timer is seen first. A fire asks
# the wake decision (never held: a stream whose provider holds no clock);
# a stall ends the stream there, a sleep moves the timer. An event needs
# at most two fires (the one armed before it and one re-arm): a loop that
# needs more is stuck.

# how an event ends: the stream stalled at `at`, the event came with the
# timer k after it, or the timer needed a third fire
type Arrive is Data:
  ArrStall{at: Nat}
  ArrCame{k: Nat}
  ArrStuck{}

def arrive.fire2(+last: Nat, +k: Nat, w: R.Wake) -> Arrive:
  match w:
    case R.WakeStall{}:
      ArrStall{Nat.add(last, k)}
    case R.WakeSleep{s}:
      ArrStuck{}

def arrive.after(on: Bool, +g: Nat, +d: Nat, +last: Nat, +k: Nat) -> Arrive:
  match on:
    case False{}:
      ArrCame{Nat.sub(k, g)}
    case True{}:
      arrive.fire2(last, k, R.idle.wake(False{}, k, d))

def arrive.fire1(+g: Nat, +d: Nat, +last: Nat, +k: Nat, w: R.Wake) -> Arrive:
  match w:
    case R.WakeStall{}:
      ArrStall{Nat.add(last, k)}
    case R.WakeSleep{+s}:
      arrive.after(Nat.is_gt(g, Nat.add(k, s)), g, d, last, Nat.add(k, s))

def arrive.first(late: Bool, +g: Nat, +d: Nat, +last: Nat, +k: Nat) -> Arrive:
  match late:
    case False{}:
      ArrCame{Nat.sub(k, g)}
    case True{}:
      arrive.fire1(g, d, last, k, R.idle.wake(False{}, k, d))

# an event g after the one at last, with the timer k after last
def arrive(+g: Nat, +d: Nat, +last: Nat, +k: Nat) -> Arrive:
  arrive.first(Nat.is_gt(g, k), g, d, last, k)

def arrive.left(a: Arrive) -> Nat:
  match a:
    case ArrStall{at}:
      0n
    case ArrCame{k}:
      k
    case ArrStuck{}:
      0n

def silent.fire2(+last: Nat, +k: Nat, w: R.Wake) -> Maybe<&2, R.Idle>:
  match w:
    case R.WakeStall{}:
      Some{R.IdleStall{Nat.add(last, k)}}
    case R.WakeSleep{s}:
      None{}

def silent.fire1(+d: Nat, +last: Nat, +k: Nat, w: R.Wake) -> Maybe<&2, R.Idle>:
  match w:
    case R.WakeStall{}:
      Some{R.IdleStall{Nat.add(last, k)}}
    case R.WakeSleep{+s}:
      silent.fire2(last, Nat.add(k, s), R.idle.wake(False{}, Nat.add(k, s), d))

# no event comes any more: the timer fires until it stalls (twice at most)
def silent(+d: Nat, +last: Nat, +k: Nat) -> Maybe<&2, R.Idle>:
  silent.fire1(d, last, k, R.idle.wake(False{}, k, d))

def drive.sel(a: Arrive, rest: List<&2, Nat>, +now: Nat, next: Maybe<&2, R.Idle>) -> Maybe<&2, R.Idle>:
  match a:
    case ArrStall{at}:
      Some{R.IdleStall{at}}
    case ArrStuck{}:
      None{}
    case ArrCame{k}:
      match rest:
        case Nil{}:
          Some{R.IdleClose{now}}
        case h <> t:
          next

# the events gs, each its gap after the one before, the first after the
# one at last; the timer k after last. The last event ends the stream.
def drive(gs: List<&2, Nat>, +d: Nat, +last: Nat, +k: Nat) -> Maybe<&2, R.Idle>:
  match gs:
    case Nil{}:
      silent(d, last, k)
    case +g <> +rest:
      +a = arrive(g, d, last, k)
      drive.sel(a, rest, Nat.add(last, g), drive(rest, d, Nat.add(last, g), arrive.left(a)))

def drive.start(w: R.Wake, gs: List<&2, Nat>, +d: Nat) -> Maybe<&2, R.Idle>:
  match w:
    case R.WakeStall{}:
      Some{R.IdleStall{0n}}
    case R.WakeSleep{k}:
      drive(gs, d, 0n, k)

# a stream armed at 0 under a deadline of d, whose events come gs apart:
# the timer is armed by the wake decision at the arming (since 0)
def drive.run(gs: List<&2, Nat>, +d: Nat) -> Maybe<&2, R.Idle>:
  drive.start(R.idle.wake(False{}, 0n, d), gs, d)

# The entry
# ---------
# bend/ffi_retry_idle.bend `ffi`, called from Rust through crate
# eukhe-bend (crates/eukhe-bend/src/rules/retry.rs). Rust saturates the
# time since the last life at the wire's largest Nat; a deadline is at most
# 2^31 - 1 ms in us, far inside the wire.

# a request, as the laws read it
type idle.Ask is Data:
  idle.AskArm{nan: Bool, neg: Bool, whole: Nat, frac: Bool}
  idle.AskWake{held: Bool, since: Nat, d: Nat}

# the request Rust writes for a, from the wire's primitives
def spell_ask(a: idle.Ask) -> String:
  match a:
    case idle.AskArm{nan, neg, whole, frac}:
      Wr.put_nat(0n, Wr.put_bool(nan, Wr.put_bool(neg, Wr.put_nat(whole, Wr.put_bool(frac, "")))))
    case idle.AskWake{held, since, d}:
      Wr.put_nat(1n, Wr.put_bool(held, Wr.put_nat(since, Wr.put_nat(d, ""))))

def spell_wake(w: R.Wake) -> String:
  match w:
    case R.WakeStall{}:
      Wr.put_nat(0n, "")
    case R.WakeSleep{us}:
      Wr.put_nat(1n, Wr.put_nat(us, ""))

# the reply to a: the spec's decision, spelled
def spell_answer(a: idle.Ask) -> String:
  match a:
    case idle.AskArm{nan, neg, whole, frac}:
      Wr.put_bool(arm_spec(nan, neg, whole, frac), "")
    case idle.AskWake{held, since, d}:
      spell_wake(wake_spec(held, since, d))

# every number of a fits the wire (and so does every reply's number)
def ask_fits(a: idle.Ask) -> Bool:
  match a:
    case idle.AskArm{nan, neg, whole, frac}:
      LawsBase.wire_fits(whole)
    case idle.AskWake{held, since, d}:
      Bool.and(LawsBase.wire_fits(since), LawsBase.wire_fits(d))

# The laws' reader
# ----------------

def read_arm.frac(nan: Bool, neg: Bool, whole: Nat, r: Wr.Dec<Bool>) -> Wr.Dec<idle.Ask>:
  match r:
    case Wr.Got{frac, s}:
      Wr.Got{idle.AskArm{nan, neg, whole, frac}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_arm.whole(nan: Bool, neg: Bool, r: Wr.Dec<Nat>) -> Wr.Dec<idle.Ask>:
  match r:
    case Wr.Got{whole, s}:
      read_arm.frac(nan, neg, whole, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_arm.neg(nan: Bool, r: Wr.Dec<Bool>) -> Wr.Dec<idle.Ask>:
  match r:
    case Wr.Got{neg, s}:
      read_arm.whole(nan, neg, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_arm(r: Wr.Dec<Bool>) -> Wr.Dec<idle.Ask>:
  match r:
    case Wr.Got{nan, s}:
      read_arm.neg(nan, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_wake.d(held: Bool, since: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<idle.Ask>:
  match r:
    case Wr.Got{d, s}:
      Wr.Got{idle.AskWake{held, since, d}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_wake.since(held: Bool, r: Wr.Dec<Nat>) -> Wr.Dec<idle.Ask>:
  match r:
    case Wr.Got{since, s}:
      read_wake.d(held, since, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_wake(r: Wr.Dec<Bool>) -> Wr.Dec<idle.Ask>:
  match r:
    case Wr.Got{held, s}:
      read_wake.since(held, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_ask.tag(t: Nat, s: String) -> Wr.Dec<idle.Ask>:
  match t:
    case 0n:
      read_arm(Wr.get_bool(s))
    case 1n:
      read_wake(Wr.get_bool(s))
    case 2n+p:
      Wr.Bad{}

def read_ask.go(r: Wr.Dec<Nat>) -> Wr.Dec<idle.Ask>:
  match r:
    case Wr.Got{t, s}:
      read_ask.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def read_ask.end(whole: Bool, a: idle.Ask) -> Maybe<&2, idle.Ask>:
  match whole:
    case True{}:
      Some{a}
    case False{}:
      None{}

def read_ask.whole(r: Wr.Dec<idle.Ask>) -> Maybe<&2, idle.Ask>:
  match r:
    case Wr.Got{a, s}:
      read_ask.end(Wr.end(s), a)
    case Wr.Bad{}:
      None{}

# the request s is, when s is exactly one request
def read_ask(s: String) -> Maybe<&2, idle.Ask>:
  read_ask.whole(read_ask.go(Wr.get_nat(s)))

# Laws
# ----

# LAW idle_wake_exact: when the deadline's timer fires, a held clock sleeps a whole deadline (a queue is not a stall); a free clock stalls once the deadline has passed since the stream's last life, and else sleeps exactly what is left of it
# EXCLUDES: a stall while held, a stall before the deadline, a re-arm past
#   the deadline or short of it, a timer that never stalls
law idle_wake_exact:
  for held: Bool
  for since: Nat
  for d: Nat
  {R.idle.wake(held, since, d) == wake_spec(held, since, d) : R.Wake}

# LAW idle_arm_exact: a deadline is armed exactly when stream_idle_timeout_ms is a number above 0: NaN, a negative number and 0 disable it, any positive number (a fraction too) arms it
# EXCLUDES: a NaN or negative timeout that arms, a fraction below 1 that
#   disables, a positive timeout that disables
law idle_arm_exact:
  for nan: Bool
  for neg: Bool
  for whole: Nat
  for frac: Bool
  {R.idle.arm(nan, neg, whole, frac) == arm_spec(nan, neg, whole, frac) : Bool}

# LAW idle_wake_refines: the timer loop driven by the wake decision ends every stream exactly as the idle model (R.idle): under every positive deadline, for every gap list, stalled or closed at the same time, never stuck (at most two fires per event)
# EXCLUDES: a wake decision whose loop stalls early or late, misses a
#   stall, re-arms from the timer instead of the last life, or fires
#   more than twice per event
law idle_wake_refines:
  for gs: List<&2, Nat>
  for +d: Nat
  for positive: {Nat.is_gt(d, 0n) == True{} : Bool}
  {drive.run(gs, d) == Some{R.idle(gs, d)} : Maybe<&2, R.Idle>}

# LAW retry_idle_entry_answers: on every request Rust writes whose numbers fit the wire, spelled from the wire's primitives, the entry answers the spelled decision: whether the deadline is armed, or what the timer does when it fires
# EXCLUDES: a codec that loses, swaps or misreads a field, a reply of
#   another decision or in another spelling
law retry_idle_entry_answers:
  for +a: idle.Ask
  for fits: {ask_fits(a) == True{} : Bool}
  {Fi.ffi(spell_ask(a)) == spell_answer(a) : String}

# LAW retry_idle_entry_malformed_exact: every input that is not exactly one request (the laws' reader finds none, or input is left after it) gets exactly the error form 'E ', then "retry_idle: malformed request"
# EXCLUDES: a default decision for input that is no request, trailing
#   input ignored, another error text than the one Rust reports
law retry_idle_entry_malformed_exact:
  for +s: String
  for no: {read_ask(s) == None{} : Maybe<&2, idle.Ask>}
  {Fi.ffi(s) == SCon{'E', SCon{' ', "retry_idle: malformed request"}} : String}

# LAW retry_idle_entry_example: anchor: the strings Rust sends: a timeout of 300 ms, 0.5 ms, 0, a negative one and NaN; a fire 0 and 250 after the last life under 1000, one at the deadline, a held one; input left over is refused
# EXCLUDES: another spelling of the requests or replies Rust reads
law retry_idle_entry_example:
  {[Fi.ffi("0,FF300,F"), Fi.ffi("0,FF0,T"), Fi.ffi("0,FF0,F"), Fi.ffi("0,FT5,F"), Fi.ffi("0,TF0,F"), Fi.ffi("1,F0,1000,"), Fi.ffi("1,F250,1000,"), Fi.ffi("1,F1000,1000,"), Fi.ffi("1,T4000,1000,"), Fi.ffi("1,F0,1000,x")] == ["T", "T", "F", "F", "F", "1,1000,", "1,750,", "0,", "1,1000,", "E retry_idle: malformed request"] : List<&2, String>}

# LAW retry_idle_req_fits_example: witness: requests of each kind fit the wire (retry_idle_entry_answers is not vacuous), and a stream of events within the deadline closes when its provider ends it
# EXCLUDES: a vacuous ask_fits or positive premise
law retry_idle_req_fits_example:
  {[ask_fits(idle.AskArm{False{}, False{}, 300n, False{}}), ask_fits(idle.AskWake{False{}, 250n, 1000n})] == [True{}, True{}] : List<&2, Bool>} & {drive.run([3n, 2n], 5n) == Some{R.IdleClose{5n}} : Maybe<&2, R.Idle>}

# The model the bridge reads, pinned
# ----------------------------------
# idle_wake_refines ties the timer's decisions to `R.idle` only for
# deadlines above 0, and no law fixed `R.idle` itself: a second fresh
# adversary (SpecCheckRetry) filled it to read a deadline of 0 as none
# (`R.idle([5n], 0n)` closing at 5 instead of stalling at 0), and every
# law checked. `R.idle` is the oracle the bridge test runs the real timer
# loop against, so it is pinned here for every deadline.

# the end when the event g after the one at last is past the deadline d
def idle_spec.at(late: Bool, +d: Nat, +last: Nat, then: R.Idle) -> R.Idle:
  match late:
    case True{}:
      R.IdleStall{Nat.add(last, d)}
    case False{}:
      then

# the events after the one at last, each its gap after the one before:
# the stream stalls d after the last event before the first gap above d,
# or closes at its last event
def idle_spec.go(gs: List<&2, Nat>, +d: Nat, +last: Nat) -> R.Idle:
  match gs:
    case Nil{}:
      R.IdleClose{last}
    case +g <> rest:
      idle_spec.at(Nat.is_gt(g, d), d, last, idle_spec.go(rest, d, Nat.add(last, g)))

# a stream armed at 0 whose events come gs apart (R3); with no event it
# stalls at d
def idle_spec(gs: List<&2, Nat>, +d: Nat) -> R.Idle:
  match gs:
    case Nil{}:
      R.IdleStall{d}
    case +g <> rest:
      idle_spec.go(g <> rest, d, 0n)

# LAW idle_exact: for every deadline (0 too) and every gaps, the model the bridge reads ends a
# stream as R3 says: a stall d after the last event before the first gap above d, a stall at d
# with no event, else a close at the last event
# EXCLUDES: a model that reads some deadline as none, stalls early or late, or closes a stalled
#   stream (the bridge would then check the timer loop against a wrong oracle)
law idle_exact:
  for +gs: List<&2, Nat>
  for +d: Nat
  {R.idle(gs, d) == idle_spec(gs, d) : R.Idle}
