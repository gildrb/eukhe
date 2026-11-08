# eukhe: the laws of area retry_idle

import Base
import ../bend/ffi_retry_idle.bend as Fi
import ../bend/retry.bend as R
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# ---- retry_idle ----

# LAWS (RI, the stream-idle deadline): when a provider stream that shows
# no life stalls (crates/eukhe-ai/src/utils/stream_idle.rs). The deadline
# of one stream runs as the stepper of bend/ffi_retry_idle.bend (the model
# of bend/retry.bend section 6): Rust (`StreamIdle`) opens it with the
# facts of the timeout and the deadline, sends each event of the stream's
# life as it comes (a provider event, a hold of its clock and its end, the
# timer firing) with its time, sleeps as the answer says and aborts on a
# stall. However threads and tokio order those events, they are the
# stepper's input: the laws below hold for every sequence of them.
# PROOF.bend proves these laws (as RetryIdle.<law>) with the lemmas of
# proof/retry_idle/.

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

# The stepper, as section 6 states it
# -----------------------------------
# One event (R.IdleEv, its time in us since the deadline was armed) moves
# the state of one stream's deadline (R.IdleSt: the deadline d in us, the
# stream's latest life, the holds alive, stalled): a life moves the
# latest life to the later of it and the event's time; a hold counts one
# more hold; the end of a hold counts one fewer (never below none) and
# moves the latest life like a life; a fire asks the timer's decision
# (wake_spec), the clock held while a hold is alive, `now - last` after
# the latest life (0 when the fire's time is before it), and a stall ends
# the deadline. Only a fire answers. An ended deadline answers nothing.

def step_spec.fire(+d: Nat, +last: Nat, +holds: Nat, w: R.Wake) -> R.IdleSt & Maybe<&2, R.Wake>:
  match w:
    case R.WakeStall{}:
      (R.IdleSt{d, last, holds, True{}}, Some{R.WakeStall{}})
    case R.WakeSleep{us}:
      (R.IdleSt{d, last, holds, False{}}, Some{R.WakeSleep{us}})

def step_spec.live(+d: Nat, +last: Nat, +holds: Nat, e: R.IdleEv) -> R.IdleSt & Maybe<&2, R.Wake>:
  match e:
    case R.IdleLife{now}:
      (R.IdleSt{d, Nat.max(last, now), holds, False{}}, None{})
    case R.IdleHold{}:
      (R.IdleSt{d, last, 1n+holds, False{}}, None{})
    case R.IdleFree{now}:
      (R.IdleSt{d, Nat.max(last, now), Nat.sub(holds, 1n), False{}}, None{})
    case R.IdleFire{now}:
      step_spec.fire(d, last, holds, wake_spec(Nat.is_gt(holds, 0n), Nat.sub(now, last), d))

def step_spec(s: R.IdleSt, e: R.IdleEv) -> R.IdleSt & Maybe<&2, R.Wake>:
  match s:
    case R.IdleSt{d, last, holds, over}:
      match over:
        case True{}:
          (R.IdleSt{d, last, holds, True{}}, None{})
        case False{}:
          step_spec.live(d, last, holds, e)

def ri_mst(r: R.IdleSt & Maybe<&2, R.Wake>) -> R.IdleSt:
  (s, m) = r
  s

def ri_mans(r: R.IdleSt & Maybe<&2, R.Wake>) -> Maybe<&2, R.Wake>:
  (s, m) = r
  m

# The entry
# ---------
# bend/ffi_retry_idle.bend, a stepper Rust runs through crate eukhe-bend
# (crates/eukhe-bend/src/rules/retry.rs `Idle`). Rust saturates every time
# at the wire's largest Nat; a deadline is at most 2^31 - 1 ms in us, far
# inside the wire.

# the open Rust writes: the facts of stream_idle_timeout_ms (NaN,
# negative, its whole part, a fraction), then the deadline in us
def spell_open(nan: Bool, neg: Bool, whole: Nat, frac: Bool, d: Nat) -> String:
  Wr.put_bool(nan, Wr.put_bool(neg, Wr.put_nat(whole, Wr.put_bool(frac, Wr.put_nat(d, "")))))

# an event Rust writes: 0 a life, 1 a hold, 2 the end of a hold, 3 a fire
def spell_ev(e: R.IdleEv) -> String:
  match e:
    case R.IdleLife{now}:
      Wr.put_nat(0n, Wr.put_nat(now, ""))
    case R.IdleHold{}:
      Wr.put_nat(1n, "")
    case R.IdleFree{now}:
      Wr.put_nat(2n, Wr.put_nat(now, ""))
    case R.IdleFire{now}:
      Wr.put_nat(3n, Wr.put_nat(now, ""))

def spell_wake(w: R.Wake) -> String:
  match w:
    case R.WakeStall{}:
      Wr.put_nat(0n, "")
    case R.WakeSleep{us}:
      Wr.put_nat(1n, Wr.put_nat(us, ""))

# a reply Rust reads: 0 nothing to do, 1 then the timer's decision
def spell_reply(m: Maybe<&2, R.Wake>) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, "")
    case Some{w}:
      Wr.put_nat(1n, spell_wake(w))

# the time an event carries fits the wire
def ev_fits(e: R.IdleEv) -> Bool:
  match e:
    case R.IdleLife{now}:
      LawsBase.wire_fits(now)
    case R.IdleHold{}:
      True{}
    case R.IdleFree{now}:
      LawsBase.wire_fits(now)
    case R.IdleFire{now}:
      LawsBase.wire_fits(now)

def evs_fit(es: List<&2, R.IdleEv>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case e <> rest:
      Bool.and(ev_fits(e), evs_fit(rest))

# the open's answer: an armed deadline is the model's open, answered with
# its first decision; an unarmed one is shut and answers nothing
def open_spec(armed: Bool, +d: Nat) -> Fi.St & String:
  match armed:
    case True{}:
      (Fi.Live{ri_mst(R.idle.open(d))}, spell_reply(ri_mans(R.idle.open(d))))
    case False{}:
      (Fi.Shut{}, Wr.put_nat(0n, ""))

# The laws' readers
# -----------------

def read_open.end(whole: Bool, o: Fi.Open) -> Maybe<&2, Fi.Open>:
  match whole:
    case True{}:
      Some{o}
    case False{}:
      None{}

def read_open.d(nan: Bool, neg: Bool, whole: Nat, frac: Bool, r: Wr.Dec<Nat>) -> Maybe<&2, Fi.Open>:
  match r:
    case Wr.Got{d, s}:
      read_open.end(Wr.end(s), Fi.Open{nan, neg, whole, frac, d})
    case Wr.Bad{}:
      None{}

def read_open.frac(nan: Bool, neg: Bool, whole: Nat, r: Wr.Dec<Bool>) -> Maybe<&2, Fi.Open>:
  match r:
    case Wr.Got{frac, s}:
      read_open.d(nan, neg, whole, frac, Wr.get_nat(s))
    case Wr.Bad{}:
      None{}

def read_open.whole(nan: Bool, neg: Bool, r: Wr.Dec<Nat>) -> Maybe<&2, Fi.Open>:
  match r:
    case Wr.Got{whole, s}:
      read_open.frac(nan, neg, whole, Wr.get_bool(s))
    case Wr.Bad{}:
      None{}

def read_open.neg(nan: Bool, r: Wr.Dec<Bool>) -> Maybe<&2, Fi.Open>:
  match r:
    case Wr.Got{neg, s}:
      read_open.whole(nan, neg, Wr.get_nat(s))
    case Wr.Bad{}:
      None{}

def read_open.go(r: Wr.Dec<Bool>) -> Maybe<&2, Fi.Open>:
  match r:
    case Wr.Got{nan, s}:
      read_open.neg(nan, Wr.get_bool(s))
    case Wr.Bad{}:
      None{}

# the open s is, when s is exactly one open
def read_open(s: String) -> Maybe<&2, Fi.Open>:
  read_open.go(Wr.get_bool(s))

def read_ev.fin(whole: Bool, e: R.IdleEv) -> Maybe<&2, R.IdleEv>:
  match whole:
    case True{}:
      Some{e}
    case False{}:
      None{}

def read_ev.end(s: String, e: R.IdleEv) -> Maybe<&2, R.IdleEv>:
  read_ev.fin(Wr.end(s), e)

def read_ev.life(r: Wr.Dec<Nat>) -> Maybe<&2, R.IdleEv>:
  match r:
    case Wr.Got{now, s}:
      read_ev.end(s, R.IdleLife{now})
    case Wr.Bad{}:
      None{}

def read_ev.free(r: Wr.Dec<Nat>) -> Maybe<&2, R.IdleEv>:
  match r:
    case Wr.Got{now, s}:
      read_ev.end(s, R.IdleFree{now})
    case Wr.Bad{}:
      None{}

def read_ev.fire(r: Wr.Dec<Nat>) -> Maybe<&2, R.IdleEv>:
  match r:
    case Wr.Got{now, s}:
      read_ev.end(s, R.IdleFire{now})
    case Wr.Bad{}:
      None{}

def read_ev.tag(t: Nat, s: String) -> Maybe<&2, R.IdleEv>:
  match t:
    case 0n:
      read_ev.life(Wr.get_nat(s))
    case 1n:
      read_ev.end(s, R.IdleHold{})
    case 2n:
      read_ev.free(Wr.get_nat(s))
    case 3n:
      read_ev.fire(Wr.get_nat(s))
    case 4n+p:
      None{}

def read_ev.go(r: Wr.Dec<Nat>) -> Maybe<&2, R.IdleEv>:
  match r:
    case Wr.Got{t, s}:
      read_ev.tag(t, s)
    case Wr.Bad{}:
      None{}

# the event s is, when s is exactly one event
def read_ev(s: String) -> Maybe<&2, R.IdleEv>:
  read_ev.go(Wr.get_nat(s))

# Histories
# ---------

def ri_state(r: Fi.St & String) -> Fi.St:
  (s, x) = r
  s

def ri_reply(r: Fi.St & String) -> String:
  (s, x) = r
  x

# the stepper after the events es, spelled
def ri_feed(es: List<&2, R.IdleEv>, st: Fi.St) -> Fi.St:
  match es:
    case Nil{}:
      st
    case e <> rest:
      ri_feed(rest, ri_state(Fi.step(st, spell_ev(e))))

# the stepper as Rust opens it for a deadline of d us (a timeout that
# arms: 1 ms, no fraction)
def ri_opened(d: Nat) -> Fi.St:
  ri_state(Fi.open(spell_open(False{}, False{}, 1n, False{}, d)))

# no reply to the events es was a stall
def ri_quiet(es: List<&2, R.IdleEv>, +st: Fi.St) -> Bool:
  match es:
    case Nil{}:
      True{}
    case +e <> rest:
      Bool.and(Bool.not(String.eq(ri_reply(Fi.step(st, spell_ev(e))), "1,0,")), ri_quiet(rest, ri_state(Fi.step(st, spell_ev(e)))))

# the latest life es report after acc: lives and ends of holds
def ri_latest(es: List<&2, R.IdleEv>, acc: Nat) -> Nat:
  match es:
    case Nil{}:
      acc
    case e <> rest:
      match e:
        case R.IdleLife{now}:
          ri_latest(rest, Nat.max(acc, now))
        case R.IdleHold{}:
          ri_latest(rest, acc)
        case R.IdleFree{now}:
          ri_latest(rest, Nat.max(acc, now))
        case R.IdleFire{now}:
          ri_latest(rest, acc)

# the holds alive after es, from acc: a hold counts one, its end one off
def ri_holds(es: List<&2, R.IdleEv>, acc: Nat) -> Nat:
  match es:
    case Nil{}:
      acc
    case e <> rest:
      match e:
        case R.IdleLife{now}:
          ri_holds(rest, acc)
        case R.IdleHold{}:
          ri_holds(rest, 1n+acc)
        case R.IdleFree{now}:
          ri_holds(rest, Nat.sub(acc, 1n))
        case R.IdleFire{now}:
          ri_holds(rest, acc)

# The host's loop over the stepper
# --------------------------------
# The loop of `StreamIdle::within` with the stepper: the timer fires `k`
# after the stream's last event (at `last`); an event that comes at or
# before the timer is seen first. Each event is a life sent at its time,
# each fire a fire sent at its time, to the stepper's state after the
# events before (a stream whose provider holds no clock); the host sleeps
# as it answers. The loop's shape is `drive` above: its wake decisions
# and its event times come from the stepper.

# the timer's decision the stepper answers a fire k after the last event
# at last (a stall when it answers none: it had already stalled)
def sd.wake.of(m: Maybe<&2, R.Wake>) -> R.Wake:
  match m:
    case None{}:
      R.WakeStall{}
    case Some{w}:
      w

def sd.wake(+d: Nat, +last: Nat, +k: Nat) -> R.Wake:
  sd.wake.of(ri_mans(R.idle.step(R.IdleSt{d, last, 0n, False{}}, R.IdleFire{Nat.add(last, k)})))

# the stream's latest life in the stepper after an event g after last
def sd.last(s: R.IdleSt) -> Nat:
  match s:
    case R.IdleSt{d, last, holds, over}:
      last

def sd.life(+d: Nat, +last: Nat, +g: Nat) -> Nat:
  sd.last(ri_mst(R.idle.step(R.IdleSt{d, last, 0n, False{}}, R.IdleLife{Nat.add(last, g)})))

def sd.arrive.fire2(+last: Nat, +k: Nat, w: R.Wake) -> Arrive:
  match w:
    case R.WakeStall{}:
      ArrStall{Nat.add(last, k)}
    case R.WakeSleep{s}:
      ArrStuck{}

def sd.arrive.after(on: Bool, +g: Nat, +d: Nat, +last: Nat, +k: Nat) -> Arrive:
  match on:
    case False{}:
      ArrCame{Nat.sub(k, g)}
    case True{}:
      sd.arrive.fire2(last, k, sd.wake(d, last, k))

def sd.arrive.fire1(+g: Nat, +d: Nat, +last: Nat, +k: Nat, w: R.Wake) -> Arrive:
  match w:
    case R.WakeStall{}:
      ArrStall{Nat.add(last, k)}
    case R.WakeSleep{+s}:
      sd.arrive.after(Nat.is_gt(g, Nat.add(k, s)), g, d, last, Nat.add(k, s))

def sd.arrive.first(late: Bool, +g: Nat, +d: Nat, +last: Nat, +k: Nat) -> Arrive:
  match late:
    case False{}:
      ArrCame{Nat.sub(k, g)}
    case True{}:
      sd.arrive.fire1(g, d, last, k, sd.wake(d, last, k))

def sd.arrive(+g: Nat, +d: Nat, +last: Nat, +k: Nat) -> Arrive:
  sd.arrive.first(Nat.is_gt(g, k), g, d, last, k)

def sd.silent.fire2(+last: Nat, +k: Nat, w: R.Wake) -> Maybe<&2, R.Idle>:
  match w:
    case R.WakeStall{}:
      Some{R.IdleStall{Nat.add(last, k)}}
    case R.WakeSleep{s}:
      None{}

def sd.silent.fire1(+d: Nat, +last: Nat, +k: Nat, w: R.Wake) -> Maybe<&2, R.Idle>:
  match w:
    case R.WakeStall{}:
      Some{R.IdleStall{Nat.add(last, k)}}
    case R.WakeSleep{+s}:
      sd.silent.fire2(last, Nat.add(k, s), sd.wake(d, last, Nat.add(k, s)))

def sd.silent(+d: Nat, +last: Nat, +k: Nat) -> Maybe<&2, R.Idle>:
  sd.silent.fire1(d, last, k, sd.wake(d, last, k))

def sd.drive(gs: List<&2, Nat>, +d: Nat, +last: Nat, +k: Nat) -> Maybe<&2, R.Idle>:
  match gs:
    case Nil{}:
      sd.silent(d, last, k)
    case +g <> +rest:
      +a = sd.arrive(g, d, last, k)
      drive.sel(a, rest, sd.life(d, last, g), sd.drive(rest, d, sd.life(d, last, g), arrive.left(a)))

def sd.drive.start(w: Maybe<&2, R.Wake>, gs: List<&2, Nat>, +d: Nat) -> Maybe<&2, R.Idle>:
  match w:
    case None{}:
      None{}
    case Some{v}:
      match v:
        case R.WakeStall{}:
          Some{R.IdleStall{0n}}
        case R.WakeSleep{k}:
          sd.drive(gs, d, 0n, k)

# a stream whose deadline of d Rust opens at 0, whose events come gs
# apart: the timer is armed as the open answers
def sd.run(gs: List<&2, Nat>, +d: Nat) -> Maybe<&2, R.Idle>:
  sd.drive.start(ri_mans(R.idle.open(d)), gs, d)

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

# LAW idle_step_exact: the model's step is section 6 as stated: a life or the end of a hold moves the latest life to the later time, a hold counts, the end of a hold uncounts (never below none), a fire answers the timer's decision from the latest life with the clock held while a hold is alive and a stall ends the deadline; only a fire answers, and an ended deadline answers nothing
# EXCLUDES: a life that moves the clock back (events out of order), a
#   hold that is lost or never ends, a fire that answers from the timer
#   instead of the latest life, a second stall, a stall revived
law idle_step_exact:
  for +s: R.IdleSt
  for +e: R.IdleEv
  {R.idle.step(s, e) == step_spec(s, e) : R.IdleSt & Maybe<&2, R.Wake>}

# LAW idle_open_exact: the model's open is a fresh deadline (no life but the arming at 0, no hold, not stalled) and a fire at 0: the timer's first decision
# EXCLUDES: a deadline armed from another time than its arming, or with
#   a hold or a stall already counted
law idle_open_exact:
  for +d: Nat
  {R.idle.open(d) == step_spec(R.IdleSt{d, 0n, 0n, False{}}, R.IdleFire{0n}) : R.IdleSt & Maybe<&2, R.Wake>}

# LAW idle_step_is_model: in every state, every event Rust spells (its time within the wire) moves the stepper as the model's step and answers the spelled decision of that step
# EXCLUDES: a misread event or time, a reply in another spelling, a state
#   that drifts from the model's
law idle_step_is_model:
  for +s: R.IdleSt
  for +e: R.IdleEv
  for fits: {ev_fits(e) == True{} : Bool}
  {Fi.step(Fi.Live{s}, spell_ev(e)) == (Fi.Live{ri_mst(R.idle.step(s, e))}, spell_reply(ri_mans(R.idle.step(s, e)))) : Fi.St & String}

# LAW retry_idle_entry_answers: every open Rust spells (its numbers within the wire) arms exactly what idle.arm arms: an armed deadline is the model's open, answered with the timer's first decision; an unarmed one is shut and answers nothing to do
# EXCLUDES: a codec that loses, swaps or misreads a fact or the deadline,
#   a deadline armed for a timeout that disables it, a first decision
#   other than the model's
law retry_idle_entry_answers:
  for +nan: Bool
  for +neg: Bool
  for +whole: Nat
  for +frac: Bool
  for +d: Nat
  for fits: {Bool.and(LawsBase.wire_fits(whole), LawsBase.wire_fits(d)) == True{} : Bool}
  {Fi.open(spell_open(nan, neg, whole, frac, d)) == open_spec(R.idle.arm(nan, neg, whole, frac), d) : Fi.St & String}

# LAW idle_fire_exact: whatever events came before, in any order, a fire of a deadline that has not stalled answers the timer's decision from the history: held while more holds started than ended, `now - latest` after the latest life any event reported (the arming at 0 included)
# EXCLUDES: a stall before the deadline after the latest life, a stall
#   while held, a lost stall (a fire past the deadline that sleeps), a
#   re-arm past or short of the deadline, a life moved back by a late
#   event
law idle_fire_exact:
  for +d: Nat
  for +pre: List<&2, R.IdleEv>
  for +now: Nat
  for fits: {Bool.and(LawsBase.wire_fits(d), Bool.and(LawsBase.wire_fits(now), evs_fit(pre))) == True{} : Bool}
  for positive: {Nat.is_gt(d, 0n) == True{} : Bool}
  for quiet: {ri_quiet(pre, ri_opened(d)) == True{} : Bool}
  {ri_reply(Fi.step(ri_feed(pre, ri_opened(d)), spell_ev(R.IdleFire{now}))) == spell_reply(Some{wake_spec(Nat.is_gt(ri_holds(pre, 0n), 0n), Nat.sub(now, ri_latest(pre, 0n)), d)}) : String}

# LAW idle_stalls_once: whatever inputs come between, a deadline that answered a stall answers every later event nothing
# EXCLUDES: a second stall (a double abort of the request), a stalled
#   deadline re-armed by a late event
law idle_stalls_once:
  for +d: Nat
  for +pre: List<&2, R.IdleEv>
  for +e: R.IdleEv
  for +mid: List<&2, R.IdleEv>
  for +e2: R.IdleEv
  for fits: {ev_fits(e2) == True{} : Bool}
  for stalled: {ri_reply(Fi.step(ri_feed(pre, ri_opened(d)), spell_ev(e))) == "1,0," : String}
  {ri_reply(Fi.step(ri_feed(List.append(&2, R.IdleEv, pre, e <> mid), ri_opened(d)), spell_ev(e2))) == "0," : String}

# LAW idle_only_fires_answer: in every state, a life, a hold and the end of a hold answer nothing to do
# EXCLUDES: a timer moved or a stall decided by an event that is not the
#   timer firing
law idle_only_fires_answer:
  for +s: R.IdleSt
  for +now: Nat
  for fits: {LawsBase.wire_fits(now) == True{} : Bool}
  {[ri_reply(Fi.step(Fi.Live{s}, spell_ev(R.IdleLife{now}))), ri_reply(Fi.step(Fi.Live{s}, spell_ev(R.IdleHold{}))), ri_reply(Fi.step(Fi.Live{s}, spell_ev(R.IdleFree{now})))] == ["0,", "0,", "0,"] : List<&2, String>}

# LAW idle_step_refines: the host's timer loop over the stepper (each event a life sent at its time, each fire a fire sent at its time, sleeping as the stepper answers) ends every stream exactly as the idle model: under every positive deadline, for every gap list, stalled or closed at the same time, never stuck
# EXCLUDES: a stepper whose loop stalls early or late, misses a stall,
#   re-arms from the timer instead of the last life, or never ends
law idle_step_refines:
  for gs: List<&2, Nat>
  for +d: Nat
  for positive: {Nat.is_gt(d, 0n) == True{} : Bool}
  {sd.run(gs, d) == Some{R.idle(gs, d)} : Maybe<&2, R.Idle>}

# LAW retry_idle_entry_reads: in every state, an event the laws' reader reads (whole, its time within the wire) is answered as that event spelled; an open it reads opens as that open spelled
# EXCLUDES: an input read otherwise by the entry than by the wire's grammar
law retry_idle_entry_reads:
  for +s: R.IdleSt
  for +i: String
  for +e: R.IdleEv
  for got: {read_ev(i) == Some{e} : Maybe<&2, R.IdleEv>}
  for fits: {ev_fits(e) == True{} : Bool}
  {Fi.step(Fi.Live{s}, i) == Fi.step(Fi.Live{s}, spell_ev(e)) : Fi.St & String}

# LAW retry_idle_open_reads: an open the laws' reader reads (whole, its numbers within the wire) opens as that open spelled
# EXCLUDES: an open read otherwise by the entry than by the wire's grammar
law retry_idle_open_reads:
  for +i: String
  for +nan: Bool
  for +neg: Bool
  for +whole: Nat
  for +frac: Bool
  for +d: Nat
  for got: {read_open(i) == Some{Fi.Open{nan, neg, whole, frac, d}} : Maybe<&2, Fi.Open>}
  for fits: {Bool.and(LawsBase.wire_fits(whole), LawsBase.wire_fits(d)) == True{} : Bool}
  {Fi.open(i) == Fi.open(spell_open(nan, neg, whole, frac, d)) : Fi.St & String}

# LAW retry_idle_entry_malformed_exact: in every state, an input the laws' reader does not read as exactly one event keeps the state and answers exactly the error form 'E ', then "retry_idle: malformed event"; an open it does not read is shut with "retry_idle: malformed open"; a shut stepper answers every step "retry_idle: no deadline"
# EXCLUDES: a guessed event or deadline for garbage, trailing input
#   ignored, a state moved by garbage, another error text
law retry_idle_entry_malformed_exact:
  for +s: R.IdleSt
  for +i: String
  for no: {read_ev(i) == None{} : Maybe<&2, R.IdleEv>}
  for +o: String
  for no_open: {read_open(o) == None{} : Maybe<&2, Fi.Open>}
  for +x: String
  {Fi.step(Fi.Live{s}, i) == (Fi.Live{s}, SCon{'E', SCon{' ', "retry_idle: malformed event"}}) : Fi.St & String} & {Fi.open(o) == (Fi.Shut{}, SCon{'E', SCon{' ', "retry_idle: malformed open"}}) : Fi.St & String} & {Fi.step(Fi.Shut{}, x) == (Fi.Shut{}, SCon{'E', SCon{' ', "retry_idle: no deadline"}}) : Fi.St & String}

# LAW retry_idle_entry_example: anchor: the strings Rust sends and reads: opens for 300 ms over 100 us, for 0 ms, for NaN, a short open; on 100 us a fire at 25, a life at 40, a hold then a fire at 400 (held), a fire at 100 (stalled), a fire after the stall, a bad tag, input left over; a step of a shut stepper
# EXCLUDES: another spelling of the requests or replies Rust reads
law retry_idle_entry_example:
  {[ri_reply(Fi.open("FF300,F100,")), ri_reply(Fi.open("FF0,F100,")), ri_reply(Fi.open("TF0,F5,")), ri_reply(Fi.open("FF300,F"))] == ["1,1,100,", "0,", "0,", "E retry_idle: malformed open"] : List<&2, String>} & {[ri_reply(Fi.step(ri_opened(100n), "3,25,")), ri_reply(Fi.step(ri_opened(100n), "0,40,")), ri_reply(Fi.step(ri_feed([R.IdleHold{}], ri_opened(100n)), "3,400,")), ri_reply(Fi.step(ri_opened(100n), "3,100,")), ri_reply(Fi.step(ri_feed([R.IdleFire{100n}], ri_opened(100n)), "3,500,")), ri_reply(Fi.step(ri_opened(100n), "4,")), ri_reply(Fi.step(ri_opened(100n), "3,0,x")), ri_reply(Fi.step(Fi.Shut{}, "3,0,"))] == ["1,1,75,", "0,", "1,1,100,", "1,0,", "0,", "E retry_idle: malformed event", "E retry_idle: malformed event", "E retry_idle: no deadline"] : List<&2, String>}

# LAW retry_idle_req_fits_example: witness: the premises of the laws above hold for real inputs (a deadline above 0 with a hold and a life that fit, quiet), and a stream of events within the deadline closes when its provider ends it
# EXCLUDES: vacuous fits, positive or quiet premises
law retry_idle_req_fits_example:
  {[Bool.and(LawsBase.wire_fits(100n), Bool.and(LawsBase.wire_fits(25n), evs_fit([R.IdleHold{}, R.IdleLife{40n}]))), ri_quiet([R.IdleHold{}, R.IdleLife{40n}, R.IdleFire{90n}], ri_opened(100n)), Nat.is_gt(100n, 0n)] == [True{}, True{}, True{}] : List<&2, Bool>} & {drive.run([3n, 2n], 5n) == Some{R.IdleClose{5n}} : Maybe<&2, R.Idle>} & {sd.run([3n, 2n], 5n) == Some{R.IdleClose{5n}} : Maybe<&2, R.Idle>}

# The model the timer loop refines, pinned
# ----------------------------------------
# idle_wake_refines and idle_step_refines tie the timer's decisions to
# `R.idle` only for deadlines above 0, and no law fixed `R.idle` itself: a
# second fresh adversary (SpecCheckRetry) filled it to read a deadline of 0
# as none (`R.idle([5n], 0n)` closing at 5 instead of stalling at 0), and
# every law checked. `R.idle` is the oracle the host's loop over the
# stepper is proven against, so it is pinned here for every deadline.

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

# LAW idle_exact: for every deadline (0 too) and every gaps, the idle model ends a
# stream as R3 says: a stall d after the last event before the first gap above d, a stall at d
# with no event, else a close at the last event
# EXCLUDES: a model that reads some deadline as none, stalls early or late, or closes a stalled
#   stream (idle_step_refines would then tie the timer loop to a wrong oracle)
law idle_exact:
  for +gs: List<&2, Nat>
  for +d: Nat
  {R.idle(gs, d) == idle_spec(gs, d) : R.Idle}
