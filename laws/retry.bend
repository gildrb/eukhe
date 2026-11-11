# eukhe: the laws of area retry

import Base
import ../bend/ffi_retry.bend as Fr
import ../bend/retry.bend as R
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# ---- retry ----

# LAWS (R, retries): when the harness sends a failed request again
# (audit H2, H3, H4, H5, H10, M3, M4). Each law is an open claim about
# the model in bend/retry.bend or its entry bend/ffi_retry.bend;
# PROOF.bend proves them (as Retry.<law>) with the lemmas of proof/retry/.
# The classifier, the wait, the failover walk and the stall run as this
# model, compiled (bend/ffi_retry.bend, R7; Rust calls
# eukhe_bend::rules::retry). The deferred job runs as
# bend/run/decision.bend, compiled (bend/ffi_run.bend; the run area's laws
# tie it to R.step). The idle deadline's decisions run compiled too
# (bend/ffi_retry_idle.bend, laws/retry_idle.bend).
#
# Requirements
# ------------
# R1 The classifier (crates/eukhe-ai/src/utils/retry.rs module doc and
#    `FailureFacts::retryable`): a failure the quota park ended, or a
#    quota, billing or admission limit (or a refused server wait), is never
#    retried; else the recorded HTTP status decides (408, 409, 429 and every
#    status of 500 or more are retried, no other); else the recorded typed
#    kind (a transient kind is retried, a permanent one never); else (no
#    kind, or Unknown) the text.
# R2 The wait (`retry_wait`, `RetryWait::of`, RetryDelay doc): a full-jitter
#    draw, uniform in [0, step), where the step of retry `attempt` is the
#    base doubled per retry before it, at most the cap; never before the
#    server's wait; a server wait above a positive cap refuses the retry
#    (a cap of 0: no cap on the server's wait).
# R3 The failover walk (crates/eukhe-core/src/durable/models/failover.rs
#    `next_switch` doc): while a provider of the chain was not tried, the
#    next such one in chain order after the last, at once; once every one
#    was tried, the next one in chain order after the last whose return
#    wait is positive and at most maxDelayMs, that wait being the backoff
#    (baseDelayMs doubled per earlier return, capped at maxDelayMs) and
#    never less than the server's wait of that provider's last failure;
#    never the provider that just failed; None once maxRetries switches
#    were made or no provider may be tried.
# R4 The deferred job (crates/eukhe-durable/src/harness/generation/
#    deferred.rs, generation.rs `classify`): no request goes out while a
#    job is live; a failed poll polls the same job again (one more failure
#    in a row) when the classifier retries it, the failures in a row are
#    below retry.maxRetries and time is left, else cancels it; a deferred
#    reply polls again gap+1 ms later while time is left (the failures in a
#    row start over), else cancels; no poll at or after the deadline; an
#    answer settles; a failure with no job is sent again when retryable,
#    else the request quits.
# R5 The stall (deferred.rs `idle_after_stall`): the retry of a stalled
#    stream gets twice the idle deadline it stalled under.
# R6 The idle deadline (crates/eukhe-ai/src/utils/stream_idle.rs
#    `StreamIdle::within`): a stream with no event for the deadline ends as
#    stalled the deadline after its last event; a stream whose provider
#    ends it in time closes at its last event.
# R7 The entry (bend/ffi_retry.bend `ffi`) decodes a request of the wire
#    format (crates/eukhe-bend/WIRE.md) and answers the model's decision.
# R8 The entry spelled from the wire's primitives (laws/retry_ffi.bend).
# A1 Rust saturates the base, the cap and the server's waits at the wire's
#    largest Nat (crates/eukhe-bend/src/rules/retry.rs): a saturated value
#    decides the same (the *_saturation_exact laws).

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

# LAW retry_only_retryable (R1): a retried failure that recorded a status recorded 500 or
# more, or 408, 409 or 429
law retry_only_retryable:
  for parked: Bool
  for limit: Bool
  for kind: Maybe<&2, R.Cause>
  for text: Bool
  for s: Nat
  for retried: {R.retryable(R.Facts{parked, limit, Some{s}, kind, text}) == True{} : Bool}
  {Bool.or(Nat.is_ge(s, 500n), Bool.or(Nat.is_eq(s, 408n), Bool.or(Nat.is_eq(s, 409n), Nat.is_eq(s, 429n)))) == True{} : Bool}

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

# LAW retry_listed_statuses (R1): a recorded 408 (request timeout), 409 (conflict) or 429 (too
# many requests) is retried when no park and no limit stop it, whatever the kind and the text
# EXCLUDES: a listed status not retried (a 429 read as a client error)
law retry_listed_statuses:
  for kind: Maybe<&2, R.Cause>
  for text: Bool
  {[R.retryable(R.Facts{False{}, False{}, Some{408n}, kind, text}), R.retryable(R.Facts{False{}, False{}, Some{409n}, kind, text}), R.retryable(R.Facts{False{}, False{}, Some{429n}, kind, text})] == [True{}, True{}, True{}] : List<&2, Bool>}

# The kinds of R1, row by row. Transient (the provider or the stream
# failed; a retry may cure it): Overloaded, RateLimit, ServerError,
# StreamDrop, StreamStalled, StreamRepeating (crates/eukhe-ai/src/types.rs
# stream_idle_timeout_ms and stream_repeat_limit docs, utils/stream_idle.rs
# and utils/stream_repeat.rs module docs: a stall and a repeat are
# re-issued by the retry policy; utils/retry/tests.rs
# `the_status_then_the_kind_decide`: an overloaded failure is retried).
# Permanent (the request, its content or the account is at fault; the same
# request fails again): Refusal, Safety, PaymentRequired, Auth, Permission,
# InvalidRequest, MalformedResponse (tests.rs
# `the_status_then_the_kind_decide` and
# `a_client_error_is_never_retried_by_its_text`: auth and invalid_request
# are not retried). Unknown names no cause: the text decides (tests.rs
# `the_status_then_the_kind_decide`: an unknown kind with a transient text
# is retried).

# LAW retry_transient_kinds (R1): with no park, no limit and no status, a transient kind is
# retried, whatever the text
# EXCLUDES: a transient kind not retried (a stall, a drop or a repeat that ends the run)
law retry_transient_kinds:
  for text: Bool
  {[R.retryable(R.Facts{False{}, False{}, None{}, Some{R.Overloaded{}}, text}), R.retryable(R.Facts{False{}, False{}, None{}, Some{R.RateLimit{}}, text}), R.retryable(R.Facts{False{}, False{}, None{}, Some{R.ServerError{}}, text}), R.retryable(R.Facts{False{}, False{}, None{}, Some{R.StreamDrop{}}, text}), R.retryable(R.Facts{False{}, False{}, None{}, Some{R.StreamStalled{}}, text}), R.retryable(R.Facts{False{}, False{}, None{}, Some{R.StreamRepeating{}}, text})] == [True{}, True{}, True{}, True{}, True{}, True{}] : List<&2, Bool>}

# LAW retry_permanent_kinds (R1): a permanent kind is never retried, whatever the text
# EXCLUDES: a refusal, a safety stop, an auth or permission error, a bad request or a
#   malformed response retried (the same request sent again to fail again)
law retry_permanent_kinds:
  for text: Bool
  {[R.retryable(R.Facts{False{}, False{}, None{}, Some{R.Refusal{}}, text}), R.retryable(R.Facts{False{}, False{}, None{}, Some{R.Safety{}}, text}), R.retryable(R.Facts{False{}, False{}, None{}, Some{R.PaymentRequired{}}, text}), R.retryable(R.Facts{False{}, False{}, None{}, Some{R.Auth{}}, text}), R.retryable(R.Facts{False{}, False{}, None{}, Some{R.Permission{}}, text}), R.retryable(R.Facts{False{}, False{}, None{}, Some{R.InvalidRequest{}}, text}), R.retryable(R.Facts{False{}, False{}, None{}, Some{R.MalformedResponse{}}, text})] == [False{}, False{}, False{}, False{}, False{}, False{}, False{}] : List<&2, Bool>}

# LAW retry_text_decides (R1): with no park, no limit, no status and no kind (or the Unknown
# kind), the text decides: a failure is retried exactly when its text names a transient failure
# EXCLUDES: an Unknown kind that does not fall to the text, a failure that records nothing
#   retried (or refused) whatever its text says
law retry_text_decides:
  for text: Bool
  {[R.retryable(R.Facts{False{}, False{}, None{}, None{}, text}), R.retryable(R.Facts{False{}, False{}, None{}, Some{R.Unknown{}}, text})] == [text, text] : List<&2, Bool>}

# LAW retry_classifier_example: anchors of the classifier: a 429 is retried; a status of 200
# with a transient kind is not (the status decides); an Unknown kind with a transient text is;
# an Auth kind with a transient text is not; a parked 503 is not
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

# the step of retry `attempt` (1 for the first retry), as R2 states it:
# the base doubled per retry before it, at most the cap
def rs.step(+base: Nat, attempt: Nat, +cap: Nat) -> Nat:
  Nat.min(rs.twice(Nat.sub(attempt, 1n), base), cap)

# the retry goes out (it is not refused), before `bound` ms
def rs.before(w: R.Delay, +bound: Nat) -> Bool:
  match w:
    case R.After{ms}:
      Nat.is_lt(ms, bound)
    case R.Refused{server, cap}:
      False{}

# The wait of a retry, end to end (`retry_wait`: the jitter of the draw
# under the step, with the server's wait and the cap). With no server
# wait the laws below fix it for every draw: 0 under a step of 0, else the
# draw itself below the step and the same one step later (so the draw
# modulo the step).

# LAW retry_wait_zero_step (R2): with no server wait, a policy whose base or cap is 0 retries at
# once
# EXCLUDES: a wait drawn from nothing when the policy asks for none, a refusal with no server wait
law retry_wait_zero_step:
  for base: Nat
  for attempt: Nat
  for cap: Nat
  for draw: Nat
  for none: {Bool.or(Nat.is_eq(base, 0n), Nat.is_eq(cap, 0n)) == True{} : Bool}
  {R.retry_wait(base, attempt, cap, draw, None{}) == R.After{0n} : R.Delay}

# LAW retry_wait_jitter_below_step (R2): with no server wait and a positive step, the retry goes
# out, before its step ends (a full jitter lies in [0, step))
# EXCLUDES: a jitter at or past the step, a refusal with no server wait
law retry_wait_jitter_below_step:
  for base: Nat
  for attempt: Nat
  for cap: Nat
  for draw: Nat
  for positive: {Nat.is_gt(rs.step(base, attempt, cap), 0n) == True{} : Bool}
  {rs.before(R.retry_wait(base, attempt, cap, draw, None{}), rs.step(base, attempt, cap)) == True{} : Bool}

# LAW retry_wait_jitter_spread (R2): with no server wait, a draw below the step waits that draw:
# every wait in [0, step) is reachable
# EXCLUDES: a constant jitter (no spread), a jitter that never reaches part of the step, a draw
#   scaled or shifted
law retry_wait_jitter_spread:
  for base: Nat
  for attempt: Nat
  for cap: Nat
  for j: Nat
  for below: {Nat.is_lt(j, rs.step(base, attempt, cap)) == True{} : Bool}
  {R.retry_wait(base, attempt, cap, j, None{}) == R.After{j} : R.Delay}

# LAW retry_wait_jitter_periodic (R2): with no server wait, a draw one step later waits the same:
# with retry_wait_jitter_spread, the wait is the draw modulo the step, so a draw uniform over
# whole steps gives a jitter uniform in [0, step) (a draw uniform in [0, 2^46) does up to
# step/2^46)
# EXCLUDES: a draw clamped at the step instead of wrapped (every large draw waiting the longest),
#   a jitter that favours part of the step
law retry_wait_jitter_periodic:
  for base: Nat
  for attempt: Nat
  for cap: Nat
  for draw: Nat
  {R.retry_wait(base, attempt, cap, Nat.add(rs.step(base, attempt, cap), draw), None{}) == R.retry_wait(base, attempt, cap, draw, None{}) : R.Delay}

# LAW retry_wait_server_within (R2): a server wait within the cap (or under no cap, 0) never
# refuses the retry and only lengthens its own wait (with no server wait, ms) to the server's:
# it waits the longer of the two
# EXCLUDES: a refusal with no cap or within it, a retry before the server's wait, a wait that
#   adds the two or ignores the jitter
law retry_wait_server_within:
  for base: Nat
  for attempt: Nat
  for cap: Nat
  for draw: Nat
  for s: Nat
  for ms: Nat
  for within: {Bool.or(Nat.is_eq(cap, 0n), Nat.is_le(s, cap)) == True{} : Bool}
  for own: {R.retry_wait(base, attempt, cap, draw, None{}) == R.After{ms} : R.Delay}
  {R.retry_wait(base, attempt, cap, draw, Some{s}) == R.After{Nat.max(ms, s)} : R.Delay}

# LAW retry_wait_server_past_cap (R2): a server wait above a positive cap refuses the retry,
# naming the server's wait and the cap, whatever the base, the attempt and the draw
# EXCLUDES: a retry that parks the caller past the cap, a refusal that names other numbers
law retry_wait_server_past_cap:
  for base: Nat
  for attempt: Nat
  for cap: Nat
  for draw: Nat
  for s: Nat
  for capped: {Nat.is_gt(cap, 0n) == True{} : Bool}
  for over: {Nat.is_gt(s, cap) == True{} : Bool}
  {R.retry_wait(base, attempt, cap, draw, Some{s}) == R.Refused{s, cap} : R.Delay}

# (R3) The failover walk
# ----------------------
# crates/eukhe-core/src/durable/models/failover.rs `next_switch`. Every
# input is free: any chain, any failed attempts, any policy. The
# attempts ts are oldest first; the last one just failed.

# a, a+1, ..., a+k-1
def rs.ints(k: Nat, +a: Nat) -> List<&2, Nat>:
  match k:
    case 0n:
      Nil{}
    case 1n+j:
      a <> rs.ints(j, 1n+a)

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

def rs.rank.pick(above: Bool, +last: Nat, +x: Nat, +len: Nat) -> Nat:
  match above:
    case True{}:
      Nat.sub(x, 1n+last)
    case False{}:
      Nat.add(x, Nat.sub(len, 1n+last))

# the place of provider x in the chain order after the provider `last`
# (R3: "the next in chain order after the last"): last+1 is first (0),
# then the chain's end, then it wraps around to 0, 1, ...; for x below len
# and other than last
def rs.rank(+last: Nat, +x: Nat, +len: Nat) -> Nat:
  rs.rank.pick(Nat.is_gt(x, last), last, x, len)

# the wait of a return to x (R3): the backoff (the base doubled per earlier
# return, the attempts past the first len, at most max), never less than
# the server's wait of x's last failure
def rs.return_wait(+x: Nat, +len: Nat, +ts: List<&2, R.Tried>, +base: Nat, +max: Nat) -> Nat:
  Nat.max(Nat.min(rs.twice(Nat.sub(rs.count(ts), len), base), max), rs.wait(x, ts, 0n))

# a return to x may go out: its wait is positive and at most max
def rs.may_return(+x: Nat, +len: Nat, +ts: List<&2, R.Tried>, +base: Nat, +max: Nat) -> Bool:
  Bool.and(Nat.is_gt(rs.return_wait(x, len, ts, base, max), 0n), Nat.is_le(rs.return_wait(x, len, ts, base, max), max))

# a switch to a provider not tried, at once
def rs.fresh_switch(m: Maybe<&2, R.Switch>, +ts: List<&2, R.Tried>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{s}:
      match s:
        case R.Switch{to, w}:
          Bool.and(Bool.not(rs.tried(to, ts)), Nat.is_eq(w, 0n))

def rs.is_switch(m: Maybe<&2, R.Switch>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{s}:
      True{}

# LAW failover_visits_once (R3): a request goes back to a provider it tried only after it tried
# every provider of its chain (0 .. len-1)
# EXCLUDES: a return while a provider of the chain was never tried
law failover_visits_once:
  for len: Nat
  for ts: List<&2, R.Tried>
  for p: R.Policy
  for to: Nat
  for w: Nat
  for got: {R.next(len, ts, p) == Some{R.Switch{to, w}} : Maybe<&2, R.Switch>}
  for tried: {rs.tried(to, ts) == True{} : Bool}
  {rs.all_tried(rs.ints(len, 0n), ts) == True{} : Bool}

# LAW failover_never_twice_in_a_row (R3): the next attempt never goes to the provider of the
# attempt that just failed (the newest)
# EXCLUDES: a switch to the provider that just failed, or a walk that starts from another attempt
law failover_never_twice_in_a_row:
  for len: Nat
  for t: R.Tried
  for rest: List<&2, R.Tried>
  for p: R.Policy
  for to: Nat
  for w: Nat
  for got: {R.next(len, t <> rest, p) == Some{R.Switch{to, w}} : Maybe<&2, R.Switch>}
  {Nat.is_eq(to, rs.newest(rest, t)) == False{} : Bool}

# LAW failover_return_waits (R3): a return to a provider the request tried waits a positive
# time, never less than the server's wait of that provider's last failure
# EXCLUDES: a return at once, a return before its server's wait, a server wait read from the
#   wrong attempt
law failover_return_waits:
  for len: Nat
  for ts: List<&2, R.Tried>
  for p: R.Policy
  for to: Nat
  for w: Nat
  for got: {R.next(len, ts, p) == Some{R.Switch{to, w}} : Maybe<&2, R.Switch>}
  for tried: {rs.tried(to, ts) == True{} : Bool}
  {Nat.is_gt(w, 0n) == True{} : Bool} & {Nat.is_ge(w, rs.wait(to, ts, 0n)) == True{} : Bool}

# LAW failover_delay_capped (R3): no switch waits longer than retry.failover.maxDelayMs
# EXCLUDES: a return that parks the request past max
law failover_delay_capped:
  for len: Nat
  for ts: List<&2, R.Tried>
  for switches: Nat
  for base: Nat
  for max: Nat
  for to: Nat
  for w: Nat
  for got: {R.next(len, ts, R.Policy{switches, base, max}) == Some{R.Switch{to, w}} : Maybe<&2, R.Switch>}
  {Nat.is_le(w, max) == True{} : Bool}

# LAW failover_bounded (R3): a request makes at most retry.failover.maxRetries switches: there is
# a next switch only while the switches made (the attempts but the first) are below it
# EXCLUDES: a switch past the budget, a budget read as one more
law failover_bounded:
  for len: Nat
  for t: R.Tried
  for rest: List<&2, R.Tried>
  for switches: Nat
  for base: Nat
  for max: Nat
  for to: Nat
  for w: Nat
  for got: {R.next(len, t <> rest, R.Policy{switches, base, max}) == Some{R.Switch{to, w}} : Maybe<&2, R.Switch>}
  {Nat.is_lt(rs.count(rest), switches) == True{} : Bool}

# LAW failover_in_chain (R3): every switch goes to a provider of the chain (below len)
# EXCLUDES: a switch to an index past the chain
law failover_in_chain:
  for len: Nat
  for ts: List<&2, R.Tried>
  for p: R.Policy
  for to: Nat
  for w: Nat
  for got: {R.next(len, ts, p) == Some{R.Switch{to, w}} : Maybe<&2, R.Switch>}
  {Nat.is_lt(to, len) == True{} : Bool}

# LAW failover_fresh_progress (R3): while switches are left and a provider of the chain was not
# tried, the request switches to a provider it did not try, at once
# EXCLUDES: no failover at all, a return while a provider was never tried, a fresh provider that
#   waits
law failover_fresh_progress:
  for len: Nat
  for t: R.Tried
  for rest: List<&2, R.Tried>
  for switches: Nat
  for base: Nat
  for max: Nat
  for x: Nat
  for budget: {Nat.is_lt(rs.count(rest), switches) == True{} : Bool}
  for chain: {Nat.is_lt(x, len) == True{} : Bool}
  for fresh: {rs.tried(x, t <> rest) == False{} : Bool}
  {rs.fresh_switch(R.next(len, t <> rest, R.Policy{switches, base, max}), t <> rest) == True{} : Bool}

# LAW failover_fresh_nearest (R3): while a provider x of the chain was not tried, the switch goes
# no later in chain order after the provider that just failed than x: to the first provider not
# tried in that order (with failover_fresh_progress: a switch, fresh, at once)
# EXCLUDES: a fresh provider skipped or taken out of chain order, a walk that restarts at 0
law failover_fresh_nearest:
  for len: Nat
  for t: R.Tried
  for rest: List<&2, R.Tried>
  for p: R.Policy
  for to: Nat
  for w: Nat
  for x: Nat
  for got: {R.next(len, t <> rest, p) == Some{R.Switch{to, w}} : Maybe<&2, R.Switch>}
  for chain: {Nat.is_lt(x, len) == True{} : Bool}
  for fresh: {rs.tried(x, t <> rest) == False{} : Bool}
  {Nat.is_le(rs.rank(rs.newest(rest, t), to, len), rs.rank(rs.newest(rest, t), x, len)) == True{} : Bool}

# LAW failover_return_backoff (R3): a return to a provider the request tried waits the backoff
# (retry.failover.baseDelayMs doubled per earlier return, the attempts past the first len, at
# most maxDelayMs), or that provider's server's wait when longer
# EXCLUDES: a backoff that does not double per return, doubles from the wrong count, ignores
#   max, or ignores the server's wait
law failover_return_backoff:
  for len: Nat
  for ts: List<&2, R.Tried>
  for switches: Nat
  for base: Nat
  for max: Nat
  for to: Nat
  for w: Nat
  for got: {R.next(len, ts, R.Policy{switches, base, max}) == Some{R.Switch{to, w}} : Maybe<&2, R.Switch>}
  for tried: {rs.tried(to, ts) == True{} : Bool}
  {w == rs.return_wait(to, len, ts, base, max) : Nat}

# LAW failover_return_progress (R3): once every provider of the chain was tried, while switches
# are left, a provider other than the one that just failed whose return may go out (a positive
# wait, at most max) gets a switch
# EXCLUDES: a walk that gives up while a return may go out
law failover_return_progress:
  for len: Nat
  for t: R.Tried
  for rest: List<&2, R.Tried>
  for switches: Nat
  for base: Nat
  for max: Nat
  for x: Nat
  for budget: {Nat.is_lt(rs.count(rest), switches) == True{} : Bool}
  for all: {rs.all_tried(rs.ints(len, 0n), t <> rest) == True{} : Bool}
  for chain: {Nat.is_lt(x, len) == True{} : Bool}
  for other: {Nat.is_eq(x, rs.newest(rest, t)) == False{} : Bool}
  for may: {rs.may_return(x, len, t <> rest, base, max) == True{} : Bool}
  {rs.is_switch(R.next(len, t <> rest, R.Policy{switches, base, max})) == True{} : Bool}

# LAW failover_return_nearest (R3): a return goes to the first provider in chain order after the
# one that just failed whose return may go out
# EXCLUDES: a return taken out of chain order, one that skips a provider it may return to
law failover_return_nearest:
  for len: Nat
  for t: R.Tried
  for rest: List<&2, R.Tried>
  for switches: Nat
  for base: Nat
  for max: Nat
  for to: Nat
  for w: Nat
  for x: Nat
  for got: {R.next(len, t <> rest, R.Policy{switches, base, max}) == Some{R.Switch{to, w}} : Maybe<&2, R.Switch>}
  for tried: {rs.tried(to, t <> rest) == True{} : Bool}
  for chain: {Nat.is_lt(x, len) == True{} : Bool}
  for other: {Nat.is_eq(x, rs.newest(rest, t)) == False{} : Bool}
  for may: {rs.may_return(x, len, t <> rest, base, max) == True{} : Bool}
  {Nat.is_le(rs.rank(rs.newest(rest, t), to, len), rs.rank(rs.newest(rest, t), x, len)) == True{} : Bool}

# LAW failover_example: anchors of the walk (base 10, max 200): the next fresh provider in
# chain order; once all were tried, a return after the doubled backoff, or the server's longer
# wait; none when every server asked for more than max
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

# (R4) The deferred job: laws/retry/deferred.bend

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

# LAW stall_retry_doubles (R5): the retry of a stalled stream gets twice the idle deadline it
# stalled under, said by steps: a deadline of 0 stays 0, and each ms more of the old deadline
# gives 2 ms more of the new one (Rust saturates the deadline at half the wire's largest Nat, so
# twice it stays a wire Nat)
# EXCLUDES: a deadline that grows by less (one ms, a fixed amount) or by
#   more than twice
law stall_retry_doubles:
  for t: Nat
  {R.stall.next(0n) == 0n : Nat} & {R.stall.next(1n+t) == Nat.add(R.stall.next(t), 2n) : Nat}

# (R6) The idle deadline
# ----------------------
# crates/eukhe-ai/src/utils/stream_idle.rs `StreamIdle::within`. Every
# input is free: any deadline, any gaps between the events (the first
# gap from the arming).

# LAW stall_detection_bounded: a watched stream ends no later than its last event before the
# deadline plus the deadline: a stall is detected in bounded time
law stall_detection_bounded:
  for gs: List<&2, Nat>
  for d: Nat
  {Nat.is_le(R.Idle.at(R.idle(gs, d)), Nat.add(R.idle.life(gs, d), d)) == True{} : Bool}

# the gaps before the first one past the deadline d
def rs.calm.keep(past: Bool, +g: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match past:
    case True{}:
      Nil{}
    case False{}:
      g <> rest

def rs.calm(gs: List<&2, Nat>, +d: Nat) -> List<&2, Nat>:
  match gs:
    case Nil{}:
      Nil{}
    case +g <> rest:
      rs.calm.keep(Nat.is_gt(g, d), g, rs.calm(rest, d))

def rs.sum(gs: List<&2, Nat>) -> Nat:
  match gs:
    case Nil{}:
      0n
    case g <> rest:
      Nat.add(g, rs.sum(rest))

# some gap of gs is past the deadline d
def rs.past(gs: List<&2, Nat>, +d: Nat) -> Bool:
  match gs:
    case Nil{}:
      False{}
    case +g <> rest:
      Bool.or(Nat.is_gt(g, d), rs.past(rest, d))

def rs.end.of(late: Bool, +gs: List<&2, Nat>, +d: Nat) -> R.Idle:
  match late:
    case True{}:
      R.IdleStall{Nat.add(rs.sum(rs.calm(gs, d)), d)}
    case False{}:
      R.IdleClose{rs.sum(gs)}

# how a stream whose events come gs apart ends under a deadline of d (R6):
# with no event, stalled at the deadline; with a gap past d, stalled d
# after the last event before that gap; else closed by its provider at
# its last event
def rs.end(gs: List<&2, Nat>, +d: Nat) -> R.Idle:
  match gs:
    case Nil{}:
      R.IdleStall{d}
    case +g <> +rest:
      rs.end.of(rs.past(g <> rest, d), g <> rest, d)

# LAW stall_ends_exact (R6): a watched stream ends as R6 states it, for every deadline and gaps:
# stalled at the deadline when no event comes; stalled d after its last event before the first
# gap past d; else closed at its last event
# EXCLUDES: a stall missed (a gap past the deadline that does not end the stream), a stall
#   detected late or early, a close at the wrong time, a silent stream that never ends
law stall_ends_exact:
  for gs: List<&2, Nat>
  for d: Nat
  {R.idle(gs, d) == rs.end(gs, d) : R.Idle}

# LAW stall_life_sums_calm (R6): the life stall_detection_bounded measures from is the time of
# the last event before the first gap past the deadline: the sum of the gaps before it (0 when
# the first gap is past it, or there is none)
# EXCLUDES: a life read as the stream's end (stall_detection_bounded then holds for any end), a
#   life past the stall, a life of 0 or of the last event whatever the gaps
law stall_life_sums_calm:
  for gs: List<&2, Nat>
  for d: Nat
  {R.idle.life(gs, d) == rs.sum(rs.calm(gs, d)) : Nat}

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
          Bool.and(Bool.and(LawsBase.wire_fits(len), Bool.and(LawsBase.wire_fits(List.length(&2, R.Tried, ts)), rs.tried_fit(ts))), Bool.and(LawsBase.wire_fits(switches), Bool.and(LawsBase.wire_fits(base), LawsBase.wire_fits(max))))
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

# LAW retry_ffi_fits_exists: witness: requests that fit exist (the premise of the laws above)
# EXCLUDES: a vacuous rs.req_fits
law retry_ffi_fits_exists:
  exs q: Fr.Req
  {rs.req_fits(q) == True{} : Bool}

# LAW retry_ffi_example: anchors of the entry's own encoders: Fr.put_req (a Bend encoder Rust does
# not run: Rust writes its requests with its own Writer, crates/eukhe-bend/src/rules/retry.rs;
# laws/retry_ffi.bend spells them from the wire's primitives) for a request per decision, and
# the replies Fr.put_delay and Fr.put_switch write (which Rust reads)
# EXCLUDES: a field order or a tag of these encoders other than the strings shown
law retry_ffi_example:
  {[Fr.put_req(Fr.QClassify{R.Facts{False{}, True{}, Some{42n}, Some{R.Unknown{}}, True{}}}, ""), Fr.put_req(Fr.QWait{100n, 4n, 200n, 7n, None{}}, ""), Fr.put_req(Fr.QFailover{3n, [R.Tried{0n, None{}}, R.Tried{1n, Some{70n}}], R.Policy{8n, 10n, 200n}}, ""), Fr.put_req(Fr.QStall{30n}, ""), Fr.put_delay(R.After{45n}, ""), Fr.put_delay(R.Refused{90n, 40n}, ""), Fr.put_switch(None{}, ""), Fr.put_switch(Some{R.Switch{1n, 20n}}, "")] == ["0,FT1,42,1,13,T", "1,100,4,200,7,0,", "2,3,2,0,0,1,1,70,8,10,200,", "3,30,", "0,45,", "1,90,40,", "0,", "1,1,20,"] : List<&2, String>}

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

# the chain in order after the provider `last`, never `last` itself:
# last+1 .. len-1, then 0 .. last-1
def rs.after(+last: Nat, +len: Nat) -> List<&2, Nat>:
  List.append(&2, Nat, rs.ints(Nat.sub(len, 1n+last), 1n+last), rs.ints(Nat.min(last, len), 0n))

# s when ok, else the pick of the rest
def rs.first(ok: Bool, +s: R.Switch, rest: Maybe<&2, R.Switch>) -> Maybe<&2, R.Switch>:
  match ok:
    case True{}:
      Some{s}
    case False{}:
      rest

# the first provider of xs whose return wait (the backoff b, never less
# than its server's wait) is positive and at most max
def rs.back(xs: List<&2, Nat>, +ts: List<&2, R.Tried>, +b: Nat, +max: Nat) -> Maybe<&2, R.Switch>:
  match xs:
    case Nil{}:
      None{}
    case +x <> rest:
      +d = Nat.max(b, rs.wait(x, ts, 0n))
      rs.first(Bool.and(Nat.is_gt(d, 0n), Nat.is_le(d, max)), R.Switch{x, d}, rs.back(rest, ts, b, max))

# the first provider of xs not tried, at once
def rs.fresh(xs: List<&2, Nat>, +ts: List<&2, R.Tried>) -> Maybe<&2, R.Switch>:
  match xs:
    case Nil{}:
      None{}
    case +x <> rest:
      rs.first(Bool.not(rs.tried(x, ts)), R.Switch{x, 0n}, rs.fresh(rest, ts))

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

# a poll of a live job with no ms left (at or after its deadline) counts
# one late poll
def rs.job.late(a: R.Act, j: R.Job) -> Nat:
  match a:
    case R.Send{}:
      0n
    case R.Poll{}:
      match j:
        case R.NoJob{}:
          0n
        case R.Live{failed, left}:
          match left:
            case 0n:
              1n
            case 1n+k:
              0n
    case R.Cancel{}:
      0n
    case R.Settle{}:
      0n
    case R.Quit{}:
      0n

# a request sent while the job before it was live counts one send
def rs.job.sent(j: R.Job, a: R.Act) -> Nat:
  match j:
    case R.NoJob{}:
      0n
    case R.Live{failed, left}:
      match a:
        case R.Send{}:
          1n
        case R.Poll{}:
          0n
        case R.Cancel{}:
          0n
        case R.Settle{}:
          0n
        case R.Quit{}:
          0n

def rs.job.count(t: R.Tally, +a: R.Act, +j: R.Job) -> R.Tally:
  match t:
    case R.Tally{sends, late}:
      R.Tally{Nat.add(sends, rs.job.sent(j, a)), Nat.add(late, rs.job.late(a, j))}

def rs.job.cancel() -> R.Step:
  R.Step{R.Cancel{}, R.NoJob{}}

# a retryable failed poll of a live job: below, the failures in a row are
# below retry.maxRetries
def rs.job.again(below: Bool, +failed: Nat, +left: Nat, +gap: Nat) -> R.Step:
  match below:
    case True{}:
      match left:
        case 0n:
          rs.job.cancel()
        case 1n+k:
          R.Step{R.Poll{}, R.Live{1n+failed, Nat.sub(1n+k, 1n+gap)}}
    case False{}:
      rs.job.cancel()

# a failed poll of a live job
def rs.job.broke(retryable: Bool, +fails: Nat, +failed: Nat, +left: Nat, +gap: Nat) -> R.Step:
  match retryable:
    case True{}:
      rs.job.again(Nat.is_lt(failed, fails), failed, left, gap)
    case False{}:
      rs.job.cancel()

# a failure with no job
def rs.job.fresh(retryable: Bool) -> R.Step:
  match retryable:
    case True{}:
      R.Step{R.Send{}, R.NoJob{}}
    case False{}:
      R.Step{R.Quit{}, R.NoJob{}}

# a deferred reply with ms left before the job's deadline
def rs.job.later(+ms: Nat, +gap: Nat) -> R.Step:
  match ms:
    case 0n:
      rs.job.cancel()
    case 1n+k:
      R.Step{R.Poll{}, R.Live{0n, Nat.sub(1n+k, 1n+gap)}}

# the deferred job's step: fails, retry.maxRetries; budget, the ms a new
# job may run; the job before the reply; the reply
def rs.job_step(+fails: Nat, +budget: Nat, job: R.Job, got: R.Got) -> R.Step:
  match job:
    case R.NoJob{}:
      match got:
        case R.Answer{}:
          R.Step{R.Settle{}, R.NoJob{}}
        case R.Later{gap}:
          rs.job.later(budget, gap)
        case R.Broke{retryable, gap}:
          rs.job.fresh(retryable)
    case R.Live{failed, left}:
      match got:
        case R.Answer{}:
          R.Step{R.Settle{}, R.NoJob{}}
        case R.Later{gap}:
          rs.job.later(left, gap)
        case R.Broke{retryable, gap}:
          rs.job.broke(retryable, fails, failed, left, gap)

def rs.step.act(s: R.Step) -> R.Act:
  match s:
    case R.Step{act, job}:
      act

def rs.step.job(s: R.Step) -> R.Job:
  match s:
    case R.Step{act, job}:
      job

# the replies gots folded through the job's step from the job before them,
# each counted with the job before it
def rs.job_run.go(gots: List<&2, R.Got>, +fails: Nat, +budget: Nat, +job: R.Job, +t: R.Tally) -> R.Tally:
  match gots:
    case Nil{}:
      t
    case g <> rest:
      +st = rs.job_step(fails, budget, job, g)
      rs.job_run.go(rest, fails, budget, rs.step.job(st), rs.job.count(t, rs.step.act(st), job))

# a request's replies from its first, with no job and nothing counted
def rs.job_run(+fails: Nat, +budget: Nat, gots: List<&2, R.Got>) -> R.Tally:
  rs.job_run.go(gots, fails, budget, R.NoJob{}, R.Tally{0n, 0n})

# LAW deferred_run_exact (R4): a request's replies, from its first, run as the fold of the
# job's step of section 4: the whole tally of sends while a job is live
# and of polls at or after its deadline
# EXCLUDES: a run that drops or reorders replies, starts from a live job,
#   counts from a nonzero tally, counts with the job after a step instead
#   of the one before it, or answers a constant tally
law deferred_run_exact:
  for +fails: Nat
  for +budget: Nat
  for gots: List<&2, R.Got>
  {R.run(fails, budget, gots) == rs.job_run(fails, budget, gots) : R.Tally}

def rs.by_kind(c: Maybe<&2, Bool>, text: Bool) -> Bool:
  match c:
    case Some{b}:
      b
    case None{}:
      text

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

# LAW failover_visits_once: a request goes back to a provider it tried only after it tried
# every provider of its chain
law failover_visits_once_orig:
  for len: Nat
  for ts: List<&2, R.Tried>
  for p: R.Policy
  {R.Switch.fresh_first(R.next(len, ts, p), len, ts) == True{} : Bool}

# LAW failover_never_twice_in_a_row: the next attempt never goes to the provider that just failed
law failover_never_twice_in_a_row_orig:
  for len: Nat
  for ts: List<&2, R.Tried>
  for p: R.Policy
  {R.Switch.not_last(R.next(len, ts, p), ts) == True{} : Bool}

# LAW failover_return_waits: a return to a provider the request tried waits a positive time,
# never less than the server's wait of that provider's last failure
law failover_return_waits_orig:
  for len: Nat
  for ts: List<&2, R.Tried>
  for p: R.Policy
  {R.Switch.return_waits(R.next(len, ts, p), ts) == True{} : Bool}

# LAW failover_delay_capped: no switch waits longer than retry.failover.maxDelayMs
law failover_delay_capped_orig:
  for len: Nat
  for ts: List<&2, R.Tried>
  for p: R.Policy
  {R.Switch.capped(R.next(len, ts, p), R.Policy.max(p)) == True{} : Bool}

# LAW failover_bounded: a request makes at most retry.failover.maxRetries switches
law failover_bounded_orig:
  for len: Nat
  for ts: List<&2, R.Tried>
  for p: R.Policy
  {R.Switch.within(R.next(len, ts, p), ts, p) == True{} : Bool}
