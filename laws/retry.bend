# eukhe: the laws of area retry

import Base
import ../bend/ffi_retry.bend as Fr
import ../bend/retry.bend as R
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# ---- retry ----

# LAWS (R, retries): when the harness sends a failed request again
# (audit H2, H3, H4, H5, H10, M3, M4). Each law is an open claim about
# the model in bend/retry.bend; PROOF.bend proves them (as Retry.<law>) with
# the lemmas of proof/retry/. The
# classifier, the wait, the failover walk and the stall run as this model,
# compiled (bend/ffi_retry.bend, R7; Rust calls eukhe_bend::rules::retry).
# The deferred job runs as bend/run/decision.bend, compiled (bend/ffi_run.bend).
# The idle deadline's decisions run compiled too (bend/ffi_retry_idle.bend,
# laws/retry_idle.bend).

# (R1) The classifier
# -------------------
# crates/eukhe-ai/src/utils/retry.rs `FailureFacts::retryable`. Every
# input is free: any status, any kind, any text.

# LAW retry_never_parked: a failure the quota park ended is never retried
law retry_never_parked:
  for limit: Bool
  for status: Maybe<&2, Nat>
  for kind: Maybe<&2, R.Cause>
  for text: Bool
  {R.retryable(R.Facts{True{}, limit, status, kind, text}) == False{} : Bool}

# LAW retry_never_limit: a quota, billing or admission limit, or a refused server wait, is
# never retried
law retry_never_limit:
  for parked: Bool
  for status: Maybe<&2, Nat>
  for kind: Maybe<&2, R.Cause>
  for text: Bool
  {R.retryable(R.Facts{parked, True{}, status, kind, text}) == False{} : Bool}

# LAW retry_never_client_error: a recorded status below 500 that is not 408, 409 or 429 (a client
# error such as 400) is never retried, whatever the kind and the text say
law retry_never_client_error:
  for parked: Bool
  for limit: Bool
  for kind: Maybe<&2, R.Cause>
  for text: Bool
  for s: Nat
  for below: {Nat.is_lt(s, 500n) == True{} : Bool}
  for not408: {Nat.is_eq(s, 408n) == False{} : Bool}
  for not409: {Nat.is_eq(s, 409n) == False{} : Bool}
  for not429: {Nat.is_eq(s, 429n) == False{} : Bool}
  {R.retryable(R.Facts{parked, limit, Some{s}, kind, text}) == False{} : Bool}

# LAW retry_only_retryable: a retried failure that recorded a status recorded a server error
# or 408, 409 or 429
law retry_only_retryable:
  for parked: Bool
  for limit: Bool
  for kind: Maybe<&2, R.Cause>
  for text: Bool
  for s: Nat
  for retried: {R.retryable(R.Facts{parked, limit, Some{s}, kind, text}) == True{} : Bool}
  {Bool.or(Nat.is_ge(s, 500n), R.status.listed(s)) == True{} : Bool}

# LAW retry_status_first: a recorded status decides alone: the kind and the text change
# nothing
law retry_status_first:
  for parked: Bool
  for limit: Bool
  for s: Nat
  for k1: Maybe<&2, R.Cause>
  for t1: Bool
  for k2: Maybe<&2, R.Cause>
  for t2: Bool
  {R.retryable(R.Facts{parked, limit, Some{s}, k1, t1}) == R.retryable(R.Facts{parked, limit, Some{s}, k2, t2}) : Bool}

# LAW retry_kind_before_text: with no status, a known kind decides alone: the text changes
# nothing
law retry_kind_before_text:
  for parked: Bool
  for limit: Bool
  for k: R.Cause
  for known: {R.Cause.known(k) == True{} : Bool}
  for t1: Bool
  for t2: Bool
  {R.retryable(R.Facts{parked, limit, None{}, Some{k}, t1}) == R.retryable(R.Facts{parked, limit, None{}, Some{k}, t2}) : Bool}

# LAW retry_server_errors: a server error (status 500 or more) is retried when no park and no
# limit stop it
law retry_server_errors:
  for kind: Maybe<&2, R.Cause>
  for text: Bool
  for s: Nat
  for server: {Nat.is_lt(s, 500n) == False{} : Bool}
  {R.retryable(R.Facts{False{}, False{}, Some{s}, kind, text}) == True{} : Bool}

# what a retry may cure by a recorded kind (`retryable_kind`): Some{True}
# for a transient kind, Some{False} for a permanent one, None for Unknown
# (the text decides)
def rs.kind(k: R.Cause) -> Maybe<&2, Bool>:
  match k:
    case R.Overloaded{}:
      Some{True{}}
    case R.RateLimit{}:
      Some{True{}}
    case R.ServerError{}:
      Some{True{}}
    case R.StreamDrop{}:
      Some{True{}}
    case R.StreamStalled{}:
      Some{True{}}
    case R.StreamRepeating{}:
      Some{True{}}
    case R.Refusal{}:
      Some{False{}}
    case R.Safety{}:
      Some{False{}}
    case R.PaymentRequired{}:
      Some{False{}}
    case R.Auth{}:
      Some{False{}}
    case R.Permission{}:
      Some{False{}}
    case R.InvalidRequest{}:
      Some{False{}}
    case R.MalformedResponse{}:
      Some{False{}}
    case R.Unknown{}:
      None{}

def rs.by_kind(c: Maybe<&2, Bool>, text: Bool) -> Bool:
  match c:
    case Some{b}:
      b
    case None{}:
      text

# a status a retry may cure (`retryable_status`): 408, 409, 429, or 500
# and above
def rs.status(+s: Nat) -> Bool:
  Bool.or(Nat.is_ge(s, 500n), Bool.or(Nat.is_eq(s, 408n), Bool.or(Nat.is_eq(s, 409n), Nat.is_eq(s, 429n))))

# with no park and no limit: the recorded status; with none, the recorded
# kind; with neither (or Unknown), the text
def rs.recorded(status: Maybe<&2, Nat>, kind: Maybe<&2, R.Cause>, text: Bool) -> Bool:
  match status kind:
    case Some{s} k:
      rs.status(s)
    case None{} Some{k}:
      rs.by_kind(rs.kind(k), text)
    case None{} None{}:
      text

# `FailureFacts::retryable`, as the Rust states it
def rs.retryable(f: R.Facts) -> Bool:
  match f:
    case R.Facts{parked, limit, status, kind, text}:
      Bool.and(Bool.not(Bool.or(parked, limit)), rs.recorded(status, kind, text))

# LAW retry_classifier_exact: the classifier decides exactly as the Rust rule: never after a park
# or a limit; else by the recorded status (408, 409, 429, 500 and above);
# else by the recorded kind (transient yes, permanent no); else (no kind,
# or Unknown) by the text
# EXCLUDES: a listed status (408, 409, 429) not retried, a transient kind
#   not retried, a permanent kind retried, an Unknown kind that does not
#   fall to the text, a text read when a status or a known kind exists
law retry_classifier_exact:
  for f: R.Facts
  {R.retryable(f) == rs.retryable(f) : Bool}

# LAW retry_classifier_example: anchors of the classifier: a 429 is retried, a 400 with a transient
# text is not, an Unknown kind with a transient text is, a park is not
# EXCLUDES: a spec helper read in a way the Rust does not mean
law retry_classifier_example:
  {[R.retryable(R.Facts{False{}, False{}, Some{429n}, None{}, False{}}), R.retryable(R.Facts{False{}, False{}, Some{200n}, Some{R.Overloaded{}}, True{}}), R.retryable(R.Facts{False{}, False{}, None{}, Some{R.Unknown{}}, True{}}), R.retryable(R.Facts{False{}, False{}, None{}, Some{R.Auth{}}, True{}}), R.retryable(R.Facts{True{}, False{}, Some{503n}, None{}, True{}})] == [True{}, False{}, True{}, False{}, False{}] : List<&2, Bool>}

# (R2) The wait
# -------------
# crates/eukhe-ai/src/utils/retry.rs `retry_wait` (the step, the jitter)
# and `RetryWait::of` (the server's wait and the cap). Rust saturates the
# base, the cap and the server's wait at the wire's largest Nat
# (`eukhe_bend::wire::NAT_MAX`, over 3000 years of ms) and draws the
# jitter uniform in [0, 2^46).

# LAW retry_after_respected: a retry never goes out before the server's requested wait
law retry_after_respected:
  for jitter: Nat
  for s: Nat
  for cap: Nat
  {R.Delay.respects(R.wait(jitter, Some{s}, cap), s) == True{} : Bool}

# LAW retry_refuses_past_cap: a server wait above a cap refuses the retry and names the server's
# time
law retry_refuses_past_cap:
  for jitter: Nat
  for s: Nat
  for cap: Nat
  for capped: {Nat.is_gt(cap, 0n) == True{} : Bool}
  for over: {Nat.is_gt(s, cap) == True{} : Bool}
  {R.wait(jitter, Some{s}, cap) == R.Refused{s, cap} : R.Delay}

# LAW retry_wait_plain: with no server wait the retry waits its jitter
# EXCLUDES: a wait invented from nothing, a refusal with no server wait
law retry_wait_plain:
  for jitter: Nat
  for cap: Nat
  {R.wait(jitter, None{}, cap) == R.After{jitter} : R.Delay}

# LAW retry_wait_uncapped: with no cap (0) the retry waits the longer of its jitter and the
# server's wait, whatever the server asked
# EXCLUDES: a refusal with no cap, a wait longer than both
law retry_wait_uncapped:
  for jitter: Nat
  for s: Nat
  {R.wait(jitter, Some{s}, 0n) == R.After{Nat.max(jitter, s)} : R.Delay}

# LAW retry_wait_within_cap: a server wait within the cap: the retry waits the longer of its
# jitter and the server's wait
# EXCLUDES: a refusal of a server wait the cap allows, a wait that adds
#   the two instead of taking the longer
law retry_wait_within_cap:
  for jitter: Nat
  for s: Nat
  for cap: Nat
  for within: {Nat.is_le(s, cap) == True{} : Bool}
  {R.wait(jitter, Some{s}, cap) == R.After{Nat.max(jitter, s)} : R.Delay}

# when the retry goes out: Some{ms}, or None when it is refused
def rs.held(w: R.Delay) -> Maybe<&2, Nat>:
  match w:
    case R.After{ms}:
      Some{ms}
    case R.Refused{server, cap}:
      None{}

# LAW retry_wait_saturation_exact: under a positive cap, a server wait saturated at any c above the
# cap decides the same: the same wait, or a refusal (Rust saturates the
# server's wait at the wire's largest Nat; only the number a refusal
# names can change, for a server wait past that)
# EXCLUDES: a saturation that turns a refusal into a retry or changes a
#   wait
law retry_wait_saturation_exact:
  for jitter: Nat
  for s: Nat
  for cap: Nat
  for c: Nat
  for capped: {Nat.is_gt(cap, 0n) == True{} : Bool}
  for above: {Nat.is_gt(c, cap) == True{} : Bool}
  {rs.held(R.wait(jitter, Some{Nat.min(s, c)}, cap)) == rs.held(R.wait(jitter, Some{s}, cap)) : Maybe<&2, Nat>}

# b doubled k times
def rs.twice(k: Nat, +b: Nat) -> Nat:
  match k:
    case 0n:
      b
    case 1n+j:
      rs.twice(j, Nat.add(b, b))

# LAW retry_step_exact: the step of retry `attempt` (1 for the first retry) is the base
# doubled per retry before it, at most the cap, for every base, attempt and
# cap (no product passes the cap: a native Nat never passes 2^48-1)
# EXCLUDES: a step that does not double, doubles once too often, ignores
#   the cap, or overflows past the cap
law retry_step_exact:
  for base: Nat
  for attempt: Nat
  for cap: Nat
  {R.jitter.step(base, attempt, cap) == Nat.min(rs.twice(Nat.sub(attempt, 1n), base), cap) : Nat}

# LAW retry_step_example: anchors of the step: base 100 under cap 600: 100, 200, 400, 600
# EXCLUDES: a step off by one retry
law retry_step_example:
  {[R.jitter.step(100n, 1n, 600n), R.jitter.step(100n, 2n, 600n), R.jitter.step(100n, 3n, 600n), R.jitter.step(100n, 4n, 600n), R.jitter.step(100n, 40n, 600n)] == [100n, 200n, 400n, 600n, 600n] : List<&2, Nat>}

# LAW retry_jitter_exact: the jitter of a draw under a positive step is the draw modulo the
# step (a draw uniform in [0, 2^46) gives a jitter uniform in [0, step) up
# to step/2^46); under a step of 0 it is 0
# EXCLUDES: a jitter at or past the step, a constant jitter (no spread)
law retry_jitter_exact:
  for step: Nat
  for draw: Nat
  for positive: {Nat.is_gt(step, 0n) == True{} : Bool}
  {R.jitter.draw(step, draw) == Nat.mod(draw, step) : Nat}

# LAW retry_jitter_zero_step: under a step of 0 (a base or a cap of 0) the jitter is 0
# EXCLUDES: a wait drawn from nothing when the policy asks for none
law retry_jitter_zero_step:
  for draw: Nat
  {R.jitter.draw(0n, draw) == 0n : Nat}

# LAW retry_wait_composes: the wait of a retry (`retry_wait`) is the wait of the jitter drawn
# under its step, with the server's wait and the cap
# EXCLUDES: a retry wait that skips the jitter, the step or the server
law retry_wait_composes:
  for base: Nat
  for attempt: Nat
  for cap: Nat
  for draw: Nat
  for server: Maybe<&2, Nat>
  {R.retry_wait(base, attempt, cap, draw, server) == R.wait(R.jitter.draw(R.jitter.step(base, attempt, cap), draw), server, cap) : R.Delay}

# (R3) The failover walk
# ----------------------
# crates/eukhe-core/src/durable/models/failover.rs `next_switch`. Every
# input is free: any chain, any failed attempts, any policy.

# LAW failover_visits_once: a request goes back to a provider it tried only after it tried
# every provider of its chain
law failover_visits_once:
  for len: Nat
  for ts: List<&2, R.Tried>
  for p: R.Policy
  {R.Switch.fresh_first(R.next(len, ts, p), len, ts) == True{} : Bool}

# LAW failover_never_twice_in_a_row: the next attempt never goes to the provider that just failed
law failover_never_twice_in_a_row:
  for len: Nat
  for ts: List<&2, R.Tried>
  for p: R.Policy
  {R.Switch.not_last(R.next(len, ts, p), ts) == True{} : Bool}

# LAW failover_return_waits: a return to a provider the request tried waits a positive time,
# never less than the server's wait of that provider's last failure
law failover_return_waits:
  for len: Nat
  for ts: List<&2, R.Tried>
  for p: R.Policy
  {R.Switch.return_waits(R.next(len, ts, p), ts) == True{} : Bool}

# LAW failover_delay_capped: no switch waits longer than retry.failover.maxDelayMs
law failover_delay_capped:
  for len: Nat
  for ts: List<&2, R.Tried>
  for p: R.Policy
  {R.Switch.capped(R.next(len, ts, p), R.Policy.max(p)) == True{} : Bool}

# LAW failover_bounded: a request makes at most retry.failover.maxRetries switches
law failover_bounded:
  for len: Nat
  for ts: List<&2, R.Tried>
  for p: R.Policy
  {R.Switch.within(R.next(len, ts, p), ts, p) == True{} : Bool}

# The failover walk as `next_switch` states it (spec helpers)

# a, a+1, ..., a+k-1
def rs.ints(k: Nat, +a: Nat) -> List<&2, Nat>:
  match k:
    case 0n:
      Nil{}
    case 1n+j:
      a <> rs.ints(j, 1n+a)

# the chain in order after the provider `last`, never `last` itself:
# last+1 .. len-1, then 0 .. last-1
def rs.after(+last: Nat, +len: Nat) -> List<&2, Nat>:
  List.append(&2, Nat, rs.ints(Nat.sub(len, 1n+last), 1n+last), rs.ints(Nat.min(last, len), 0n))

# some attempt of ts went to provider x
def rs.tried(+x: Nat, ts: List<&2, R.Tried>) -> Bool:
  match ts:
    case Nil{}:
      False{}
    case t <> rest:
      match t:
        case R.Tried{at, w}:
          Bool.or(Nat.is_eq(at, x), rs.tried(x, rest))

# every provider of xs was tried
def rs.all_tried(xs: List<&2, Nat>, +ts: List<&2, R.Tried>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> rest:
      Bool.and(rs.tried(x, ts), rs.all_tried(rest, ts))

def rs.wait.pick(hit: Bool, w: Maybe<&2, Nat>, +acc: Nat) -> Nat:
  match hit:
    case True{}:
      Maybe.default(&2, Nat, w, 0n)
    case False{}:
      acc

# the server's wait of the newest attempt at x, read oldest first (0 when
# that attempt recorded none); acc: the answer before ts
def rs.wait(+x: Nat, ts: List<&2, R.Tried>, +acc: Nat) -> Nat:
  match ts:
    case Nil{}:
      acc
    case t <> rest:
      match t:
        case R.Tried{at, w}:
          rs.wait(x, rest, rs.wait.pick(Nat.is_eq(at, x), w, acc))

# s when ok, else the pick of the rest
def rs.first(ok: Bool, +s: R.Switch, rest: Maybe<&2, R.Switch>) -> Maybe<&2, R.Switch>:
  match ok:
    case True{}:
      Some{s}
    case False{}:
      rest

# the first provider of xs not tried, at once
def rs.fresh(xs: List<&2, Nat>, +ts: List<&2, R.Tried>) -> Maybe<&2, R.Switch>:
  match xs:
    case Nil{}:
      None{}
    case +x <> rest:
      rs.first(Bool.not(rs.tried(x, ts)), R.Switch{x, 0n}, rs.fresh(rest, ts))

# the first provider of xs whose return wait (the backoff b, never less
# than its server's wait) is positive and at most max
def rs.back(xs: List<&2, Nat>, +ts: List<&2, R.Tried>, +b: Nat, +max: Nat) -> Maybe<&2, R.Switch>:
  match xs:
    case Nil{}:
      None{}
    case +x <> rest:
      +d = Nat.max(b, rs.wait(x, ts, 0n))
      rs.first(Bool.and(Nat.is_gt(d, 0n), Nat.is_le(d, max)), R.Switch{x, d}, rs.back(rest, ts, b, max))

def rs.count(ts: List<&2, R.Tried>) -> Nat:
  match ts:
    case Nil{}:
      0n
    case t <> rest:
      1n+rs.count(rest)

# the provider of the newest attempt: the last of t, ts
def rs.newest(ts: List<&2, R.Tried>, +t: R.Tried) -> Nat:
  match ts:
    case Nil{}:
      match t:
        case R.Tried{at, w}:
          at
    case u <> rest:
      rs.newest(rest, u)

# once every provider was tried: the backoff of the next return is the
# base doubled per earlier return (the attempts past the first len), at
# most max
def rs.returns(all: Bool, +last: Nat, +len: Nat, +ts: List<&2, R.Tried>, +p: R.Policy) -> Maybe<&2, R.Switch>:
  match all:
    case True{}:
      rs.back(rs.after(last, len), ts, Nat.min(rs.twice(Nat.sub(rs.count(ts), len), R.Policy.base(p)), R.Policy.max(p)), R.Policy.max(p))
    case False{}:
      rs.fresh(rs.after(last, len), ts)

# while the switches made (the attempts but the first) are below the
# budget: a fresh provider while one is left, else a return
def rs.budget(ok: Bool, +last: Nat, +len: Nat, +ts: List<&2, R.Tried>, +p: R.Policy) -> Maybe<&2, R.Switch>:
  match ok:
    case True{}:
      rs.returns(rs.all_tried(rs.ints(len, 0n), ts), last, len, ts, p)
    case False{}:
      None{}

# `next_switch`, as the Rust states it: no attempt, no switch
def rs.next(+len: Nat, ts: List<&2, R.Tried>, +p: R.Policy) -> Maybe<&2, R.Switch>:
  match ts:
    case Nil{}:
      None{}
    case +t <> +rest:
      rs.budget(Nat.is_lt(rs.count(rest), R.Policy.switches(p)), rs.newest(rest, t), len, t <> rest, p)

# LAW failover_exact: the walk decides exactly as `next_switch` states it, for every
# chain, every failed attempt list and every policy
# EXCLUDES: no failover at all (always None), a fresh provider skipped or
#   taken out of chain order, a return before every provider was tried, a
#   backoff that does not double per return or ignores max, a switch past
#   the budget or one short of it, a server wait read from the wrong attempt
law failover_exact:
  for len: Nat
  for ts: List<&2, R.Tried>
  for p: R.Policy
  {R.next(len, ts, p) == rs.next(len, ts, p) : Maybe<&2, R.Switch>}

# LAW failover_example: anchors of the walk (base 10, max 300): the next fresh provider in
# chain order; once all were tried, a return after the doubled backoff, or
# the server's longer wait; none past max, past the budget, or with no wait
# EXCLUDES: a spec helper read in a way `next_switch` does not mean
law failover_example:
  {[R.next(3n, [R.Tried{1n, None{}}], R.Policy{8n, 10n, 200n}), R.next(3n, [R.Tried{2n, None{}}], R.Policy{8n, 10n, 200n}), R.next(3n, [R.Tried{0n, None{}}, R.Tried{1n, None{}}, R.Tried{2n, None{}}], R.Policy{8n, 10n, 200n}), R.next(3n, [R.Tried{0n, None{}}, R.Tried{1n, None{}}, R.Tried{2n, None{}}, R.Tried{0n, None{}}], R.Policy{8n, 10n, 200n}), R.next(3n, [R.Tried{0n, Some{50n}}, R.Tried{1n, None{}}, R.Tried{2n, None{}}], R.Policy{8n, 10n, 200n}), R.next(3n, [R.Tried{0n, Some{250n}}, R.Tried{1n, Some{250n}}, R.Tried{2n, None{}}], R.Policy{8n, 10n, 200n})] == [Some{R.Switch{2n, 0n}}, Some{R.Switch{0n, 0n}}, Some{R.Switch{0n, 10n}}, Some{R.Switch{1n, 20n}}, Some{R.Switch{0n, 50n}}, None{}] : List<&2, Maybe<&2, R.Switch>>}

# LAW failover_budget_example: anchors of the budget and of a zero backoff: a policy of 1 switch
# allows one switch and no second; a base of 0 never returns without a
# server's wait
# EXCLUDES: a budget off by one, a return that goes out at once
law failover_budget_example:
  {[R.next(2n, [R.Tried{0n, None{}}], R.Policy{1n, 10n, 200n}), R.next(2n, [R.Tried{0n, None{}}, R.Tried{1n, None{}}], R.Policy{1n, 10n, 200n}), R.next(2n, [R.Tried{0n, None{}}, R.Tried{1n, None{}}], R.Policy{8n, 0n, 200n})] == [Some{R.Switch{1n, 0n}}, None{}, None{}] : List<&2, Maybe<&2, R.Switch>>}

def rs.cap_wait(w: Maybe<&2, Nat>, +c: Nat) -> Maybe<&2, Nat>:
  match w:
    case Some{x}:
      Some{Nat.min(x, c)}
    case None{}:
      None{}

# every server wait of ts saturated at c
def rs.cap_waits(ts: List<&2, R.Tried>, +c: Nat) -> List<&2, R.Tried>:
  match ts:
    case Nil{}:
      Nil{}
    case t <> rest:
      match t:
        case R.Tried{at, w}:
          R.Tried{at, rs.cap_wait(w, c)} <> rs.cap_waits(rest, c)

# LAW failover_wait_saturation_exact: server waits saturated at any c above max decide the same walk
# (Rust saturates them at the wire's largest Nat: exact for every max
# below it)
# EXCLUDES: a saturation that returns to a provider whose server asked for
#   more than max, or changes a switch's wait
law failover_wait_saturation_exact:
  for len: Nat
  for ts: List<&2, R.Tried>
  for p: R.Policy
  for c: Nat
  for above: {Nat.is_gt(c, R.Policy.max(p)) == True{} : Bool}
  {R.next(len, rs.cap_waits(ts, c), p) == R.next(len, ts, p) : Maybe<&2, R.Switch>}

# LAW failover_base_saturation_exact: a base saturated at any c of at least max decides the same walk
# (Rust saturates it at the wire's largest Nat: exact for every max up to
# it)
# EXCLUDES: a saturation that changes a backoff
law failover_base_saturation_exact:
  for len: Nat
  for ts: List<&2, R.Tried>
  for switches: Nat
  for base: Nat
  for max: Nat
  for c: Nat
  for at_least: {Nat.is_le(max, c) == True{} : Bool}
  {R.next(len, ts, R.Policy{switches, Nat.min(base, c), max}) == R.next(len, ts, R.Policy{switches, base, max}) : Maybe<&2, R.Switch>}

# (R4) The deferred job
# ---------------------
# crates/eukhe-durable/src/harness/generation/deferred.rs and the poll
# decisions of generation.rs `classify`. Every input is free: any
# replies, in any order.

# LAW deferred_pays_once: no request goes out while the request's deferred job is live: a
# failed poll polls the same job again or cancels it
law deferred_pays_once:
  for fails: Nat
  for budget: Nat
  for gots: List<&2, R.Got>
  {R.Tally.sends(R.run(fails, budget, gots)) == 0n : Nat}

# LAW deferred_bounded_in_time: no poll goes out at or after the job's deadline
law deferred_bounded_in_time:
  for fails: Nat
  for budget: Nat
  for gots: List<&2, R.Got>
  {R.Tally.late(R.run(fails, budget, gots)) == 0n : Nat}

# LAW deferred_failed_poll_repolls: a retryable failed poll, with fetch failures and time left, polls
# the same job again
law deferred_failed_poll_repolls:
  for fails: Nat
  for budget: Nat
  for failed: Nat
  for left: Nat
  for gap: Nat
  for below: {Nat.is_lt(failed, fails) == True{} : Bool}
  for live: {Nat.is_gt(left, 0n) == True{} : Bool}
  {R.step(fails, budget, R.Live{failed, left}, R.Broke{True{}, gap}) == R.Step{R.Poll{}, R.Live{1n+failed, Nat.sub(left, 1n+gap)}} : R.Step}

# (R5) The stall
# --------------
# crates/eukhe-durable/src/harness/generation/deferred.rs
# `idle_after_stall`.

# LAW stall_retry_extends: the retry of a stalled stream gets a longer idle deadline than the
# one it stalled under
law stall_retry_extends:
  for idle: Nat
  for positive: {Nat.is_gt(idle, 0n) == True{} : Bool}
  {Nat.is_lt(idle, R.stall.next(idle)) == True{} : Bool}

# LAW stall_retry_doubles: the retry of a stalled stream gets twice the idle deadline it
# stalled under (Rust saturates the deadline at half the wire's largest
# Nat, so twice it stays a wire Nat)
# EXCLUDES: a deadline that grows by less (one ms, a fixed amount) or by
#   more than twice
law stall_retry_doubles:
  for idle: Nat
  {R.stall.next(idle) == Nat.add(idle, idle) : Nat}

# (R6) The idle deadline
# ----------------------
# crates/eukhe-ai/src/utils/stream_idle.rs `StreamIdle::within`. Every
# input is free: any deadline, any gaps between the events.

# LAW stall_detection_bounded: a watched stream ends no later than its last event before the
# deadline plus the deadline: a stall is detected in bounded time
law stall_detection_bounded:
  for gs: List<&2, Nat>
  for d: Nat
  {Nat.is_le(R.Idle.at(R.idle(gs, d)), Nat.add(R.idle.life(gs, d), d)) == True{} : Bool}

# LAW stall_silent_ends_at_deadline: a stream that sends no event ends as stalled at the deadline
law stall_silent_ends_at_deadline:
  for d: Nat
  {R.idle(Nil{}, d) == R.IdleStall{d} : R.Idle}

# (R7) The entry of the compiled core
# -----------------------------------
# bend/ffi_retry.bend `ffi`: the classifier, the wait, the failover walk
# and the stall, called from Rust through crate eukhe-bend in the wire
# format of laws/wire.bend. Rust saturates every value (above) so
# each Nat it encodes fits the wire.

# a Maybe<Nat> fits the wire
def rs.mfits(m: Maybe<&2, Nat>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{n}:
      LawsBase.wire_fits(n)

# every attempt of ts fits the wire
def rs.tried_fit(ts: List<&2, R.Tried>) -> Bool:
  match ts:
    case Nil{}:
      True{}
    case t <> rest:
      match t:
        case R.Tried{at, w}:
          Bool.and(Bool.and(LawsBase.wire_fits(at), rs.mfits(w)), rs.tried_fit(rest))

# every Nat of a request fits the wire (and so does the count of a list)
def rs.req_fits(q: Fr.Req) -> Bool:
  match q:
    case Fr.QClassify{f}:
      match f:
        case R.Facts{parked, limit, status, kind, text}:
          rs.mfits(status)
    case Fr.QWait{base, attempt, cap, draw, server}:
      Bool.and(Bool.and(LawsBase.wire_fits(base), LawsBase.wire_fits(attempt)), Bool.and(Bool.and(LawsBase.wire_fits(cap), LawsBase.wire_fits(draw)), rs.mfits(server)))
    case Fr.QFailover{len, +ts, p}:
      match p:
        case R.Policy{switches, base, max}:
          Bool.and(Bool.and(LawsBase.wire_fits(len), Bool.and(LawsBase.wire_fits(R.length(ts)), rs.tried_fit(ts))), Bool.and(LawsBase.wire_fits(switches), Bool.and(LawsBase.wire_fits(base), LawsBase.wire_fits(max))))
    case Fr.QStall{idle}:
      LawsBase.wire_fits(idle)

# LAW retry_ffi_request_round_trip: a request that fits the wire reads back, and the rest is untouched
# EXCLUDES: a field read into the wrong slot, a lost or extra attempt, a
#   swapped Bool, a cause read as another cause, a wrong decision tag
law retry_ffi_request_round_trip:
  for q: Fr.Req
  for +rest: String
  for h: {rs.req_fits(q) == True{} : Bool}
  {Fr.get_req(Fr.put_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<Fr.Req>}

# LAW retry_ffi_request_exact: a decoded request is exactly an encoding: any other input is Bad{}
# EXCLUDES: an unknown tag, cause or Maybe mark read as a value, a request
#   read from a string that no encoder writes (a default for bad input)
law retry_ffi_request_exact:
  for +s: String
  for +q: Fr.Req
  for +rest: String
  for h: {Fr.get_req(s) == Wr.Got{q, rest} : Wr.Dec<Fr.Req>}
  {s == Fr.put_req(q, rest) : String}

# LAW retry_ffi_classify: the entry answers a classify request with the classifier's decision
# EXCLUDES: an entry that answers anything but the model's decision
law retry_ffi_classify:
  for f: R.Facts
  for h: {rs.req_fits(Fr.QClassify{f}) == True{} : Bool}
  {Fr.ffi(Fr.put_req(Fr.QClassify{f}, "")) == Wr.put_bool(R.retryable(f), "") : String}

# LAW retry_ffi_wait: the entry answers a wait request with the model's wait
# EXCLUDES: an entry that answers anything but the model's decision
law retry_ffi_wait:
  for base: Nat
  for attempt: Nat
  for cap: Nat
  for draw: Nat
  for server: Maybe<&2, Nat>
  for h: {rs.req_fits(Fr.QWait{base, attempt, cap, draw, server}) == True{} : Bool}
  {Fr.ffi(Fr.put_req(Fr.QWait{base, attempt, cap, draw, server}, "")) == Fr.put_delay(R.retry_wait(base, attempt, cap, draw, server), "") : String}

# LAW retry_ffi_failover: the entry answers a failover request with the model's next switch
# EXCLUDES: an entry that answers anything but the model's decision
law retry_ffi_failover:
  for len: Nat
  for ts: List<&2, R.Tried>
  for p: R.Policy
  for h: {rs.req_fits(Fr.QFailover{len, ts, p}) == True{} : Bool}
  {Fr.ffi(Fr.put_req(Fr.QFailover{len, ts, p}, "")) == Fr.put_switch(R.next(len, ts, p), "") : String}

# LAW retry_ffi_stall: the entry answers a stall request with the model's next deadline
# EXCLUDES: an entry that answers anything but the model's decision
law retry_ffi_stall:
  for idle: Nat
  for h: {rs.req_fits(Fr.QStall{idle}) == True{} : Bool}
  {Fr.ffi(Fr.put_req(Fr.QStall{idle}, "")) == Wr.put_nat(R.stall.next(idle), "") : String}

# LAW retry_ffi_malformed: malformed input answers the error form, never a decision
# EXCLUDES: a default decision for input that is no request
law retry_ffi_malformed:
  for +s: String
  for h: {Fr.get_req(s) == Wr.Bad{} : Wr.Dec<Fr.Req>}
  {Fr.ffi(s) == Wr.err("retry: malformed request") : String}

# LAW retry_ffi_trailing: input left after a request answers the error form
# EXCLUDES: a decision for a request followed by garbage
law retry_ffi_trailing:
  for +s: String
  for q: Fr.Req
  for rest: String
  for h: {Fr.get_req(s) == Wr.Got{q, rest} : Wr.Dec<Fr.Req>}
  for left: {Wr.end(rest) == False{} : Bool}
  {Fr.ffi(s) == Wr.err("retry: input left after the request") : String}

# LAW retry_ffi_fits_exists: witness: requests that fit exist (the premise of the laws above)
# EXCLUDES: a vacuous rs.req_fits
law retry_ffi_fits_exists:
  exs q: Fr.Req
  {rs.req_fits(q) == True{} : Bool}

# LAW retry_ffi_example: anchors of the encodings Rust writes and reads (crates/eukhe-bend
# WIRE.md): a request per decision, and the replies
# EXCLUDES: a field order or a tag that differs from the Rust side
law retry_ffi_example:
  {[Fr.put_req(Fr.QClassify{R.Facts{False{}, True{}, Some{42n}, Some{R.Unknown{}}, True{}}}, ""), Fr.put_req(Fr.QWait{100n, 4n, 200n, 7n, None{}}, ""), Fr.put_req(Fr.QFailover{3n, [R.Tried{0n, None{}}, R.Tried{1n, Some{70n}}], R.Policy{8n, 10n, 200n}}, ""), Fr.put_req(Fr.QStall{30n}, ""), Fr.put_delay(R.After{45n}, ""), Fr.put_delay(R.Refused{90n, 40n}, ""), Fr.put_switch(None{}, ""), Fr.put_switch(Some{R.Switch{1n, 20n}}, "")] == ["0,FT1,42,1,13,T", "1,100,4,200,7,0,", "2,3,2,0,0,1,1,70,8,10,200,", "3,30,", "0,45,", "1,90,40,", "0,", "1,1,20,"] : List<&2, String>}
