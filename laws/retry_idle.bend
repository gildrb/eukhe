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
#
# Requirements (RI). Sources: the Rust docs (crates/eukhe-bend/src/rules/
# retry.rs `Idle`, crates/eukhe-ai/src/utils/stream_idle.rs), bend/retry.bend
# section 6, crates/eukhe-bend/WIRE.md; where they are silent, omp's watchdog
# (/tmp/omp-src packages/ai/src/utils/idle-iterator.ts:10-16
# `normalizeIdleTimeoutMs`, :215-229 local work, :271-293 `onTimerFire`).
# R1  The timeout (stream_idle_timeout_ms) arms the deadline only when it is
#     a number above 0: NaN, a negative number and 0 disable it (omp: a
#     timeout <= 0 disables the watchdog); any positive number, a fraction
#     of a ms too, arms it, and every positive timeout arms the same
#     deadline: only the deadline d (us) sets the timer.
# R2  The armed deadline's first decision: sleep the whole deadline d from
#     the arming at 0; a deadline of 0 us stalls at once.
# R3  When the timer fires with no hold alive, it stalls once d has passed
#     since the stream's latest life, else it sleeps exactly until then
#     (omp `onTimerFire`: re-arm for the remainder, else time out).
# R4  While a hold of the stream's clock is alive (omp: pending local
#     work), a fire never stalls: it acts as if the stream had just shown
#     life (omp `extendDeadlineForLocalWork`), and the end of a hold counts
#     as life.
# R5  Events come in any order: the latest life is the latest time a life
#     or the end of a hold reported (the arming at 0 included), and the
#     holds alive are the holds started less those ended (an end with none
#     alive ends none).
# R6  A deadline stalls once: after a stall every event answers nothing.
# R7  Only a fire answers: a life, a hold and its end answer nothing to do.
# R8  The idle model R.idle (R6 of laws/retry.bend), the oracle of the
#     host's loop: a stream stalls d after its last event before its first
#     gap above d (a stream with no event at d), else closes at its last
#     event.
# R9  The host's loop (`StreamIdle::within`) over the timer's decisions,
#     for a deadline above 0, ends every stream as R.idle, and is never
#     stuck.
# R10 The wire (bend/ffi_retry_idle.bend header, WIRE.md): an open is NaN,
#     negative, the whole part, a fraction (Bools and a Nat), then d; an
#     event is 0,now (life) | 1 (hold) | 2,now (end of a hold) | 3,now
#     (fire); a reply is 0 (nothing to do) | 1 then 0 (stall) | 1 then 1,us
#     (sleep us). Only exactly one of them, every Nat within the wire,
#     is read; anything else answers the error form: a malformed open
#     shuts the stepper ("retry_idle: malformed open"), a malformed event
#     keeps the state ("retry_idle: malformed event"), a shut stepper
#     answers every step "retry_idle: no deadline".
#
# Coverage: R1 retry_idle_open_unarmed, retry_idle_open_armed_alike,
# retry_idle_entry_answers; R2 retry_idle_open_first; R3
# idle_wake_stalls_past_deadline, idle_wake_rearms_at_deadline,
# idle_fire_exact; R4 idle_wake_held_restarts, idle_fire_exact; R5
# idle_fire_exact (support: idle_fire_total); R6 idle_stalls_once, retry_idle_open_first; R7
# idle_only_fires_answer; R8 idle_model_closes, idle_model_stalls; R9
# idle_wake_refines, idle_step_refines; R10 idle_step_is_model,
# retry_idle_entry_answers, retry_idle_step_reads_spelled,
# retry_idle_step_refused, retry_idle_open_reads_spelled,
# retry_idle_open_refused. Anchors: retry_idle_entry_example,
# retry_idle_req_fits_example.

# Terms
# -----

# R3, R4 as a relation of the fire and its answer, not a formula: the
# timer fires `since` after the stream's latest life under a deadline d.
# omp `onTimerFire` (idle-iterator.ts:278-293): the deadline is the latest
# life plus d; a fire before it re-arms for exactly the time left
# (`remainingMs`: since + sleep = d), a fire at or past it times out; a
# held clock (omp `extendDeadlineForLocalWork`) counts as life just now,
# so it sleeps a whole d. w is a right answer exactly when fire_ok holds;
# some w is for every fire (idle_fire_total), and since a fire answers
# one reply, idle_fire_exact pins it.
def fire_ok(held: Bool, +since: Nat, +d: Nat, w: R.Wake) -> Bool:
  match held:
    case True{}:
      match w:
        case R.WakeStall{}:
          False{}
        case R.WakeSleep{s}:
          Nat.is_eq(s, d)
    case False{}:
      match w:
        case R.WakeStall{}:
          Nat.is_le(d, since)
        case R.WakeSleep{s}:
          Bool.and(Nat.is_lt(since, d), Nat.is_eq(Nat.add(since, s), d))

# the gaps gs are each at most the deadline d
def gaps_within(gs: List<&2, Nat>, +d: Nat) -> Bool:
  match gs:
    case Nil{}:
      True{}
    case g <> rest:
      Bool.and(Nat.is_le(g, d), gaps_within(rest, d))

# the time of the last of the events gs, each its gap after the one
# before, the first after 0: the sum of the gaps
def gaps_sum(gs: List<&2, Nat>) -> Nat:
  match gs:
    case Nil{}:
      0n
    case g <> rest:
      Nat.add(g, gaps_sum(rest))

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

# the state and the answer of a model step (R.idle.step: the state of one
# stream's deadline and what the timer does)
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

# an open's facts and deadline, spelled as Rust writes them
def spell_open_of(o: Fi.Open) -> String:
  match o:
    case Fi.Open{nan, neg, whole, frac, d}:
      spell_open(nan, neg, whole, frac, d)

# the numbers of an open fit the wire
def open_fits(o: Fi.Open) -> Bool:
  match o:
    case Fi.Open{nan, neg, whole, frac, d}:
      Bool.and(LawsBase.wire_fits(whole), LawsBase.wire_fits(d))

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

# LAW idle_wake_stalls_past_deadline (R3): a free clock (no hold alive) whose timer fires x at or past the deadline d after the stream's latest life (since = d + x) stalls, for every d and x
# EXCLUDES: a missed stall (a timer that sleeps again once the deadline
#   has passed), a stall only a further deadline later
law idle_wake_stalls_past_deadline:
  for +d: Nat
  for x: Nat
  {R.idle.wake(False{}, Nat.add(d, x), d) == R.WakeStall{} : R.Wake}

# LAW idle_wake_rearms_at_deadline (R3): a free clock (no hold alive) whose timer fires `since` after the stream's latest life, before the deadline (the deadline is since + 1 + u), sleeps exactly the 1 + u us left: it fires next at the deadline
# EXCLUDES: a stall before the deadline, a re-arm past or short of the
#   deadline (a whole deadline again, or the time that has passed)
law idle_wake_rearms_at_deadline:
  for +since: Nat
  for +u: Nat
  {R.idle.wake(False{}, since, Nat.add(since, 1n+u)) == R.WakeSleep{1n+u} : R.Wake}

# LAW idle_wake_held_restarts (R4): while a hold is alive, the timer of a deadline above 0 (1 + u) decides as a free clock whose stream showed life at that moment (since 0), however long ago the latest life was
# EXCLUDES: a stall while held (a queued or local-work stream aborted), a
#   held clock that sleeps what is left of the deadline or keeps counting
#   from the latest life
law idle_wake_held_restarts:
  for since: Nat
  for +u: Nat
  {R.idle.wake(True{}, since, 1n+u) == R.idle.wake(False{}, 0n, 1n+u) : R.Wake}

# LAW retry_idle_open_unarmed (R1): an open whose timeout is NaN (whatever its sign and value), negative, or 0 (no whole part, no fraction) arms no deadline: the stepper is shut and the open answers nothing to do, whatever the deadline (the numbers within the wire)
# EXCLUDES: a NaN, negative or zero timeout that arms a deadline (a stream
#   aborted by a watchdog the user turned off)
law retry_idle_open_unarmed:
  for +neg: Bool
  for +whole: Nat
  for +frac: Bool
  for +d: Nat
  for fits: {Bool.and(LawsBase.wire_fits(whole), LawsBase.wire_fits(d)) == True{} : Bool}
  {Fi.open(spell_open(True{}, neg, whole, frac, d)) == (Fi.Shut{}, spell_reply(None{})) : Fi.St & String} & {Fi.open(spell_open(False{}, True{}, whole, frac, d)) == (Fi.Shut{}, spell_reply(None{})) : Fi.St & String} & {Fi.open(spell_open(False{}, False{}, 0n, False{}, d)) == (Fi.Shut{}, spell_reply(None{})) : Fi.St & String}

# LAW retry_idle_open_armed_alike (R1): every timeout above 0 (a whole part above 0, with or without a fraction, or a fraction alone) opens exactly as a timeout of 1 ms: the stepper and its first answer depend only on the deadline d (the numbers within the wire)
# EXCLUDES: a positive timeout that disables the deadline (a fraction of a
#   ms read as 0), a deadline or first decision that depends on the
#   timeout's value
law retry_idle_open_armed_alike:
  for +w: Nat
  for +frac: Bool
  for +d: Nat
  for fits: {Bool.and(LawsBase.wire_fits(1n+w), LawsBase.wire_fits(d)) == True{} : Bool}
  {Fi.open(spell_open(False{}, False{}, 1n+w, frac, d)) == Fi.open(spell_open(False{}, False{}, 1n, False{}, d)) : Fi.St & String} & {Fi.open(spell_open(False{}, False{}, 0n, True{}, d)) == Fi.open(spell_open(False{}, False{}, 1n, False{}, d)) : Fi.St & String}

# LAW retry_idle_open_first (R2, R6): a timeout of 1 ms (with retry_idle_open_armed_alike: every positive one) over a deadline of 1 + e us answers sleep 1 + e, the whole deadline from the arming; over a deadline of 0 us it answers a stall at once, and then every event of any history (each time within the wire) answers nothing to do
# EXCLUDES: a first timer shorter or longer than the deadline, a zero
#   deadline that never stalls or stalls again
law retry_idle_open_first:
  for +e: Nat
  for +es: List<&2, R.IdleEv>
  for +ev: R.IdleEv
  for fits: {Bool.and(LawsBase.wire_fits(1n+e), ev_fits(ev)) == True{} : Bool}
  {ri_reply(Fi.open(spell_open(False{}, False{}, 1n, False{}, 1n+e))) == spell_reply(Some{R.WakeSleep{1n+e}}) : String} & {ri_reply(Fi.open(spell_open(False{}, False{}, 1n, False{}, 0n))) == spell_reply(Some{R.WakeStall{}}) : String} & {ri_reply(Fi.step(ri_feed(es, ri_opened(0n)), spell_ev(ev))) == spell_reply(None{}) : String}

# LAW idle_wake_refines: the timer loop driven by the wake decision ends every stream exactly as the idle model (R.idle): under every positive deadline, for every gap list, stalled or closed at the same time, never stuck (at most two fires per event)
# EXCLUDES: a wake decision whose loop stalls early or late, misses a
#   stall, re-arms from the timer instead of the last life, or fires
#   more than twice per event
law idle_wake_refines:
  for gs: List<&2, Nat>
  for +d: Nat
  for positive: {Nat.is_gt(d, 0n) == True{} : Bool}
  {drive.run(gs, d) == Some{R.idle(gs, d)} : Maybe<&2, R.Idle>}

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

# LAW idle_fire_exact: whatever events came before, in any order, a fire of a deadline that has not stalled answers the timer's decision from the history: held while more holds started than ended, `now - latest` after the latest life any event reported (the arming at 0 included); the decision is every w that fire_ok calls right (a stall at or past the deadline when free, else a sleep to exactly the deadline, a whole d when held)
# EXCLUDES: a stall before the deadline after the latest life, a stall
#   while held, a lost stall (a fire past the deadline that sleeps), a
#   re-arm past or short of the deadline, a life moved back by a late
#   event
law idle_fire_exact:
  for +d: Nat
  for +pre: List<&2, R.IdleEv>
  for +now: Nat
  for +w: R.Wake
  for fits: {Bool.and(LawsBase.wire_fits(d), Bool.and(LawsBase.wire_fits(now), evs_fit(pre))) == True{} : Bool}
  for positive: {Nat.is_gt(d, 0n) == True{} : Bool}
  for quiet: {ri_quiet(pre, ri_opened(d)) == True{} : Bool}
  for right: {fire_ok(Nat.is_gt(ri_holds(pre, 0n), 0n), Nat.sub(now, ri_latest(pre, 0n)), d, w) == True{} : Bool}
  {ri_reply(Fi.step(ri_feed(pre, ri_opened(d)), spell_ev(R.IdleFire{now}))) == spell_reply(Some{w}) : String}

# LAW idle_fire_total: support: every fire has a right answer under fire_ok (so idle_fire_exact speaks of every fire)
# EXCLUDES: a relation no answer meets, which would leave idle_fire_exact
#   vacuous at that fire
law idle_fire_total:
  for +held: Bool
  for +since: Nat
  for +d: Nat
  exs w: R.Wake
  {fire_ok(held, since, d, w) == True{} : Bool}

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

# LAW retry_idle_step_reads_spelled (R10): in every state, an input the stepper answers with no error form is exactly one event as Rust spells it (spell_ev: its tag, then its time), its time within the wire, nothing after it
# EXCLUDES: a default or guessed event for garbage, input left over
#   ignored, a second spelling of an event (a leading zero, another
#   tag), an over-long time read
law retry_idle_step_reads_spelled:
  for +s: R.IdleSt
  for +i: String
  for ok: {LawsBase.wire_opens_err(ri_reply(Fi.step(Fi.Live{s}, i))) == False{} : Bool}
  exs e: R.IdleEv
  {i == spell_ev(e) : String} & {ev_fits(e) == True{} : Bool}

# LAW retry_idle_step_refused (R10): in every state, a step answered with the error form keeps the state and answers exactly 'E ', then "retry_idle: malformed event"
# EXCLUDES: a state moved by a refused input, another error text
law retry_idle_step_refused:
  for +s: R.IdleSt
  for +i: String
  for err: {LawsBase.wire_opens_err(ri_reply(Fi.step(Fi.Live{s}, i))) == True{} : Bool}
  {Fi.step(Fi.Live{s}, i) == (Fi.Live{s}, Wr.err("retry_idle: malformed event")) : Fi.St & String}

# LAW retry_idle_open_reads_spelled (R10): an open the stepper answers with no error form is exactly one open as Rust spells it (spell_open: NaN, negative, the whole part, a fraction, then the deadline), its numbers within the wire, nothing after it
# EXCLUDES: a default or guessed deadline for garbage, input left over
#   ignored, a second spelling of an open, an over-long number read
law retry_idle_open_reads_spelled:
  for +i: String
  for ok: {LawsBase.wire_opens_err(ri_reply(Fi.open(i))) == False{} : Bool}
  exs o: Fi.Open
  {i == spell_open_of(o) : String} & {open_fits(o) == True{} : Bool}

# LAW retry_idle_open_refused (R10): an open answered with the error form shuts the stepper and answers exactly 'E ', then "retry_idle: malformed open"
# EXCLUDES: a deadline armed by a refused open, another error text
law retry_idle_open_refused:
  for +i: String
  for err: {LawsBase.wire_opens_err(ri_reply(Fi.open(i))) == True{} : Bool}
  {Fi.open(i) == (Fi.Shut{}, Wr.err("retry_idle: malformed open")) : Fi.St & String}

# LAW retry_idle_entry_example: anchor: the strings Rust sends and reads: opens for 300 ms over 100 us, for 0 ms, for NaN, a short open; on 100 us a fire at 25, a life at 40, a hold then a fire at 400 (held), a fire at 100 (stalled), a fire after the stall, a bad tag, input left over; a step of a shut stepper
# EXCLUDES: another spelling of the requests or replies Rust reads
law retry_idle_entry_example:
  {[ri_reply(Fi.open("FF300,F100,")), ri_reply(Fi.open("FF0,F100,")), ri_reply(Fi.open("TF0,F5,")), ri_reply(Fi.open("FF300,F"))] == ["1,1,100,", "0,", "0,", "E retry_idle: malformed open"] : List<&2, String>} & {[ri_reply(Fi.step(ri_opened(100n), "3,25,")), ri_reply(Fi.step(ri_opened(100n), "0,40,")), ri_reply(Fi.step(ri_feed([R.IdleHold{}], ri_opened(100n)), "3,400,")), ri_reply(Fi.step(ri_opened(100n), "3,100,")), ri_reply(Fi.step(ri_feed([R.IdleFire{100n}], ri_opened(100n)), "3,500,")), ri_reply(Fi.step(ri_opened(100n), "4,")), ri_reply(Fi.step(ri_opened(100n), "3,0,x")), ri_reply(Fi.step(Fi.Shut{}, "3,0,"))] == ["1,1,75,", "0,", "1,1,100,", "1,0,", "0,", "E retry_idle: malformed event", "E retry_idle: malformed event", "E retry_idle: no deadline"] : List<&2, String>}

# LAW retry_idle_req_fits_example: witness: the premises of the laws above hold for real inputs (a deadline above 0 with a hold and a life that fit, quiet; gaps within a deadline), and a stream of events within the deadline closes when its provider ends it
# EXCLUDES: vacuous fits, positive, quiet or within premises
law retry_idle_req_fits_example:
  {[Bool.and(LawsBase.wire_fits(100n), Bool.and(LawsBase.wire_fits(25n), evs_fit([R.IdleHold{}, R.IdleLife{40n}]))), ri_quiet([R.IdleHold{}, R.IdleLife{40n}, R.IdleFire{90n}], ri_opened(100n)), Nat.is_gt(100n, 0n), gaps_within([3n, 2n], 5n)] == [True{}, True{}, True{}, True{}] : List<&2, Bool>} & {drive.run([3n, 2n], 5n) == Some{R.IdleClose{5n}} : Maybe<&2, R.Idle>} & {sd.run([3n, 2n], 5n) == Some{R.IdleClose{5n}} : Maybe<&2, R.Idle>}

# The model the timer loop refines
# --------------------------------
# idle_wake_refines and idle_step_refines tie the timer's decisions to
# `R.idle` only for deadlines above 0; a fresh adversary (SpecCheckRetry)
# once filled `R.idle` to read a deadline of 0 as none (`R.idle([5n], 0n)`
# closing at 5 instead of stalling at 0) and every law checked. The two
# laws below state `R.idle` for every deadline, 0 too, by the shape of
# the gaps (gaps_within, gaps_sum, List.append), not by its recursion.

# LAW idle_model_closes (R8): a stream with at least one event whose every gap is at most the deadline d (0 too) closes at its last event, the sum of its gaps
# EXCLUDES: a stream with every event in time that stalls, or closes at
#   another time than its last event
law idle_model_closes:
  for +g: Nat
  for +gs: List<&2, Nat>
  for +d: Nat
  for within: {gaps_within(g <> gs, d) == True{} : Bool}
  {R.idle(g <> gs, d) == R.IdleClose{gaps_sum(g <> gs)} : R.Idle}

# LAW idle_model_stalls (R8): a stream whose first gaps pre are each at most the deadline d (0 too), then a gap g above d, stalls d after the last event of pre (at the sum of pre's gaps, plus d), whatever comes after; a stream with no event stalls at d
# EXCLUDES: a model that reads some deadline as none, stalls early or late
#   (from the late event instead of the last one in time), closes a
#   stalled stream or reads events after the stall
law idle_model_stalls:
  for +pre: List<&2, Nat>
  for +g: Nat
  for rest: List<&2, Nat>
  for +d: Nat
  for within: {gaps_within(pre, d) == True{} : Bool}
  for late: {Nat.is_gt(g, d) == True{} : Bool}
  {R.idle(List.append(&2, Nat, pre, g <> rest), d) == R.IdleStall{Nat.add(gaps_sum(pre), d)} : R.Idle} & {R.idle(Nil{}, d) == R.IdleStall{d} : R.Idle}
