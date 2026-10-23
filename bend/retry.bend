# retry: when the harness sends a failed request again (audit H2, H3,
# H4, H5, H10, M3, M4). Six decisions, each the model of one Rust
# function:
#
# 1. The classifier (crates/eukhe-ai/src/utils/retry.rs,
#    `FailureFacts::retryable`): a failure the quota park ended, or a
#    quota/billing limit, is never retried; else the HTTP status the
#    failure recorded decides; else its typed kind; else its text.
# 2. The wait (`retry_wait`): a full-jitter draw under the step (the base
#    doubled per retry, at most the cap); never before the server's wait;
#    a server wait above the cap refuses the retry.
# 3. The failover walk (crates/eukhe-core/src/durable/models/failover.rs,
#    `next_switch`): one request tries every provider of its chain once,
#    at once, before it returns to one, and a return waits the backoff and
#    the server's wait of that provider.
# 4. The deferred job (crates/eukhe-durable/src/harness/generation/
#    deferred.rs): a request answered "deferred" has one live job; a failed
#    poll polls the same job again or cancels it, and polls stop at the
#    job's deadline.
# 5. The stall (`deferred.rs` `idle_after_stall`): the retry of a stalled
#    stream gets a longer idle deadline.
# 6. The idle deadline (crates/eukhe-ai/src/utils/stream_idle.rs,
#    `StreamIdle::within`): a stream with no event for the deadline ends
#    as stalled, never later than its last event plus the deadline.
#
# LAWS.bend section retry states the laws; PROOF.bend proves them (as Laws.<law>)
# with the lemmas of PROOF.bend sections retry_policy and retry_ffi.
# Decisions 1, 2, 3 and 5 run compiled (bend/ffi_retry.bend, crate
# eukhe-bend); 4 runs compiled as bend/run/decision.bend's (bend/ffi_run.bend);
# bridge/bridge_retry.bend runs 6 against the Rust code.

import Base

# 1. The classifier
# -----------------

# the typed failure kind a stream failure records (StreamFailureKind)
type Cause is Data:
  Refusal{}
  Safety{}
  PaymentRequired{}
  Overloaded{}
  RateLimit{}
  ServerError{}
  Auth{}
  Permission{}
  InvalidRequest{}
  MalformedResponse{}
  StreamDrop{}
  StreamStalled{}
  StreamRepeating{}
  Unknown{}

# what a kind says about a retry (`retryable_kind`)
type Class is Data:
  Transient{}
  Permanent{}
  Unsure{}

def Cause.class(k: Cause) -> Class:
  match k:
    case Refusal{}:
      Permanent{}
    case Safety{}:
      Permanent{}
    case PaymentRequired{}:
      Permanent{}
    case Overloaded{}:
      Transient{}
    case RateLimit{}:
      Transient{}
    case ServerError{}:
      Transient{}
    case Auth{}:
      Permanent{}
    case Permission{}:
      Permanent{}
    case InvalidRequest{}:
      Permanent{}
    case MalformedResponse{}:
      Permanent{}
    case StreamDrop{}:
      Transient{}
    case StreamStalled{}:
      Transient{}
    case StreamRepeating{}:
      Transient{}
    case Unknown{}:
      Unsure{}

# a kind that decides by itself (not Unknown)
def Cause.known(k: Cause) -> Bool:
  match k:
    case Unknown{}:
      False{}
    case Refusal{}:
      True{}
    case Safety{}:
      True{}
    case PaymentRequired{}:
      True{}
    case Overloaded{}:
      True{}
    case RateLimit{}:
      True{}
    case ServerError{}:
      True{}
    case Auth{}:
      True{}
    case Permission{}:
      True{}
    case InvalidRequest{}:
      True{}
    case MalformedResponse{}:
      True{}
    case StreamDrop{}:
      True{}
    case StreamStalled{}:
      True{}
    case StreamRepeating{}:
      True{}

# parked: the quota park ended the failure; limit: its text or provider
# error type names a quota, billing or admission limit (or the HTTP
# layer's refused server wait); status: the HTTP status it recorded;
# kind: the kind it recorded; text: its text names a transient failure,
# word for word (`FailureFacts`)
type Facts is Data:
  Facts{parked: Bool, limit: Bool, status: Maybe<&2, Nat>, kind: Maybe<&2, Cause>, text: Bool}

# 408 request timeout, 409 conflict, 429 too many requests
def status.listed(+s: Nat) -> Bool:
  Bool.or(Nat.is_eq(s, 408n), Bool.or(Nat.is_eq(s, 409n), Nat.is_eq(s, 429n)))

def status.ok.go(lt: Bool, +s: Nat) -> Bool:
  match lt:
    case True{}:
      status.listed(s)
    case False{}:
      True{}

# a status a retry may cure (`retryable_status`): a listed one, or any
# server error
def status.ok(+s: Nat) -> Bool:
  status.ok.go(Nat.is_lt(s, 500n), s)

def by_class(c: Class, text: Bool) -> Bool:
  match c:
    case Transient{}:
      True{}
    case Permanent{}:
      False{}
    case Unsure{}:
      text

def by_kind(kind: Maybe<&2, Cause>, text: Bool) -> Bool:
  match kind:
    case Some{k}:
      by_class(Cause.class(k), text)
    case None{}:
      text

def by_status(status: Maybe<&2, Nat>, kind: Maybe<&2, Cause>, text: Bool) -> Bool:
  match status:
    case Some{s}:
      status.ok(s)
    case None{}:
      by_kind(kind, text)

def by_facts(parked: Bool, limit: Bool, status: Maybe<&2, Nat>, kind: Maybe<&2, Cause>, text: Bool) -> Bool:
  match parked limit:
    case True{} l:
      False{}
    case False{} True{}:
      False{}
    case False{} False{}:
      by_status(status, kind, text)

# whether a retry may cure the failure (`FailureFacts::retryable`)
def retryable(f: Facts) -> Bool:
  match f:
    case Facts{parked, limit, status, kind, text}:
      by_facts(parked, limit, status, kind, text)

# 2. The wait
# -----------

# After: the retry goes out after ms; Refused: the server asked for more
# than the cap, so no retry goes out (`RetryWait`)
type Delay is Data:
  After{ms: Nat}
  Refused{server: Nat, cap: Nat}

def wait.server(over: Bool, +jitter: Nat, +s: Nat, +cap: Nat) -> Delay:
  match over:
    case True{}:
      Refused{s, cap}
    case False{}:
      After{Nat.max(jitter, s)}

# the wait of a retry whose backoff drew `jitter` ms, after a failure whose
# server asked for `server` ms, under the cap (0: no cap) (`RetryWait::of`)
def wait(+jitter: Nat, server: Maybe<&2, Nat>, +cap: Nat) -> Delay:
  match server:
    case Some{+s}:
      wait.server(Bool.and(Nat.is_gt(cap, 0n), Nat.is_gt(s, cap)), jitter, s, cap)
    case None{}:
      After{jitter}

# the wait goes out no sooner than the server's time s
def Delay.respects(w: Delay, +s: Nat) -> Bool:
  match w:
    case After{ms}:
      Nat.is_ge(ms, s)
    case Refused{server, cap}:
      True{}

# b doubled k times, at most cap: min(b * 2^k, cap). A step stops once b
# is 0 or b + b passes cap, so no value passes cap (a native Nat stays
# below 2^48 when cap does) and a positive b doubles at most 48 times.
def double.halt(+b: Nat, +cap: Nat) -> Bool:
  Bool.or(Nat.is_eq(b, 0n), Nat.is_gt(b, Nat.sub(cap, b)))

# the end of a halted doubling: 0 stays 0, else b + b passed cap
def double.stop(b: Nat, +cap: Nat) -> Nat:
  match b:
    case 0n:
      0n
    case 1n+p:
      cap

def double.go(k: Nat, halt: Bool, +b: Nat, +cap: Nat) -> Nat:
  match k halt:
    case 0n h:
      Nat.min(b, cap)
    case 1n+j True{}:
      double.stop(b, cap)
    case 1n+j False{}:
      +d = Nat.add(b, b)
      double.go(j, double.halt(d, cap), d, cap)

def double(k: Nat, +b: Nat, +cap: Nat) -> Nat:
  double.go(k, double.halt(b, cap), b, cap)

# the step of retry `attempt` (1 for the first retry): base doubled per
# retry before it, at most cap (`retry_wait`)
def jitter.step(+base: Nat, attempt: Nat, +cap: Nat) -> Nat:
  double(Nat.sub(attempt, 1n), base, cap)

# the full-jitter draw under a step: a draw uniform in [0, 2^46) modulo
# the step, so in [0, step); 0 for a step of 0
def jitter.draw(step: Nat, +draw: Nat) -> Nat:
  match step:
    case 0n:
      0n
    case 1n+p:
      Nat.mod(draw, 1n+p)

# the wait of retry `attempt` (`retry_wait`) under the policy's base and
# cap (0: no cap on the server's wait): the jitter of `draw` under its
# step, never before the server's wait, refused past the cap
def retry_wait(+base: Nat, attempt: Nat, +cap: Nat, +draw: Nat, server: Maybe<&2, Nat>) -> Delay:
  wait(jitter.draw(jitter.step(base, attempt, cap), draw), server, cap)

# 3. The failover walk
# --------------------

# one failed attempt: the chain index of its provider and its server's
# wait (`Tried`)
type Tried is Data:
  Tried{at: Nat, wait: Maybe<&2, Nat>}

def Tried.at(t: Tried) -> Nat:
  match t:
    case Tried{at, wait}:
      at

# switches: retry.failover.maxRetries; base: retry.failover.baseDelayMs;
# max: retry.failover.maxDelayMs
type Policy is Data:
  Policy{switches: Nat, base: Nat, max: Nat}

def Policy.switches(p: Policy) -> Nat:
  match p:
    case Policy{switches, base, max}:
      switches

def Policy.base(p: Policy) -> Nat:
  match p:
    case Policy{switches, base, max}:
      base

def Policy.max(p: Policy) -> Nat:
  match p:
    case Policy{switches, base, max}:
      max

# the next attempt: the chain index of its provider, after delay ms
type Switch is Data:
  Switch{to: Nat, delay: Nat}

def length(ts: List<&2, Tried>) -> Nat:
  match ts:
    case Nil{}:
      0n
    case t <> rest:
      1n+length(rest)

# the attempt that just failed
def last.go(ts: List<&2, Tried>, +t: Tried) -> Tried:
  match ts:
    case Nil{}:
      t
    case u <> rest:
      last.go(rest, u)

def last(ts: List<&2, Tried>) -> Maybe<&2, Tried>:
  match ts:
    case Nil{}:
      None{}
    case t <> rest:
      Some{last.go(rest, t)}

def at_of(m: Maybe<&2, Tried>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{t}:
      Tried.at(t)

# the chain index of the attempt that just failed (0 for none)
def last_at(+ts: List<&2, Tried>) -> Nat:
  at_of(last(ts))

# a provider the request tried
def seen(+at: Nat, ts: List<&2, Tried>) -> Bool:
  match ts:
    case Nil{}:
      False{}
    case t <> rest:
      Bool.or(Nat.is_eq(Tried.at(t), at), seen(at, rest))

def server.pick(hit: Bool, w: Maybe<&2, Nat>, +acc: Nat) -> Nat:
  match hit:
    case True{}:
      Maybe.default(&2, Nat, w, 0n)
    case False{}:
      acc

# the server's wait of the provider's last failure (0 for none)
def server.go(+at: Nat, ts: List<&2, Tried>, +acc: Nat) -> Nat:
  match ts:
    case Nil{}:
      acc
    case t <> rest:
      match t:
        case Tried{a, w}:
          server.go(at, rest, server.pick(Nat.is_eq(a, at), w, acc))

def server(+at: Nat, +ts: List<&2, Tried>) -> Nat:
  server.go(at, ts, 0n)

# a, a+1, ..., a+k-1
def upto(k: Nat, +a: Nat) -> List<&2, Nat>:
  match k:
    case 0n:
      Nil{}
    case 1n+j:
      a <> upto(j, 1n+a)

# every index below len was tried
def all_seen.go(xs: List<&2, Nat>, +ts: List<&2, Tried>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> rest:
      Bool.and(seen(x, ts), all_seen.go(rest, ts))

def all_seen(+len: Nat, +ts: List<&2, Tried>) -> Bool:
  all_seen.go(upto(len, 0n), ts)

# chain order after the provider that just failed:
# last+1, ..., len-1, 0, ..., last-1; it never holds last, so no pick
# goes back at once to the provider that just failed
def order(+last: Nat, +len: Nat) -> List<&2, Nat>:
  List.append(&2, Nat, upto(Nat.sub(len, 1n+last), 1n+last), upto(Nat.min(last, len), 0n))

# the first candidate when ok, else the rest's pick
def pick.sel(ok: Bool, +s: Switch, rest: Maybe<&2, Switch>) -> Maybe<&2, Switch>:
  match ok:
    case True{}:
      Some{s}
    case False{}:
      rest

# the first provider of xs not tried yet, at once (the order holds no
# provider that just failed: it was tried)
def pick.fresh(xs: List<&2, Nat>, +ts: List<&2, Tried>) -> Maybe<&2, Switch>:
  match xs:
    case Nil{}:
      None{}
    case +x <> rest:
      pick.sel(Bool.not(seen(x, ts)), Switch{x, 0n}, pick.fresh(rest, ts))

# the first provider of xs whose return wait d (the backoff, and never
# less than its server's wait) is positive and at most max
def pick.back(xs: List<&2, Nat>, +ts: List<&2, Tried>, +backoff: Nat, +max: Nat) -> Maybe<&2, Switch>:
  match xs:
    case Nil{}:
      None{}
    case +x <> rest:
      +d = Nat.max(backoff, server(x, ts))
      pick.sel(Bool.and(Nat.is_gt(d, 0n), Nat.is_le(d, max)), Switch{x, d}, pick.back(rest, ts, backoff, max))

# the backoff of the next return: base doubled per earlier return, at
# most max
def backoff(+p: Policy, +len: Nat, +ts: List<&2, Tried>) -> Nat:
  double(Nat.sub(length(ts), len), Policy.base(p), Policy.max(p))

def next.mode(all: Bool, +last: Nat, +len: Nat, +ts: List<&2, Tried>, +p: Policy) -> Maybe<&2, Switch>:
  match all:
    case True{}:
      pick.back(order(last, len), ts, backoff(p, len, ts), Policy.max(p))
    case False{}:
      pick.fresh(order(last, len), ts)

def next.budget(ok: Bool, +last: Nat, +len: Nat, +ts: List<&2, Tried>, +p: Policy) -> Maybe<&2, Switch>:
  match ok:
    case True{}:
      next.mode(all_seen(len, ts), last, len, ts, p)
    case False{}:
      None{}

# the next attempt of a request whose chain holds len providers, after
# the failed attempts ts, oldest first (`next_switch`)
def next.last(m: Maybe<&2, Tried>, +len: Nat, +ts: List<&2, Tried>, +p: Policy) -> Maybe<&2, Switch>:
  match m:
    case None{}:
      None{}
    case Some{t}:
      next.budget(Nat.is_le(length(ts), Policy.switches(p)), Tried.at(t), len, ts, p)

def next(+len: Nat, +ts: List<&2, Tried>, +p: Policy) -> Maybe<&2, Switch>:
  next.last(last(ts), len, ts, p)

# the switch, if any, does not go to the provider that just failed
def Switch.not_last(+m: Maybe<&2, Switch>, +ts: List<&2, Tried>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{s}:
      match s:
        case Switch{to, delay}:
          Bool.not(Nat.is_eq(to, last_at(ts)))

# the switch, if it returns to a tried provider, comes after every
# provider of the chain was tried
def Switch.fresh_first(+m: Maybe<&2, Switch>, +len: Nat, +ts: List<&2, Tried>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{s}:
      match s:
        case Switch{to, delay}:
          Bool.or(Bool.not(seen(to, ts)), all_seen(len, ts))

# the switch, if it returns to a tried provider, waits a positive time,
# never less than the server's wait of that provider's last failure
def Switch.return_waits(+m: Maybe<&2, Switch>, +ts: List<&2, Tried>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{s}:
      match s:
        case Switch{to, delay}:
          Bool.or(Bool.not(seen(to, ts)), Bool.and(Nat.is_gt(delay, 0n), Nat.is_ge(delay, server(to, ts))))

# the switch waits at most max
def Switch.capped(+m: Maybe<&2, Switch>, +max: Nat) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{s}:
      match s:
        case Switch{to, delay}:
          Nat.is_le(delay, max)

# there is a switch only while the switches made are below the budget
def Switch.within(+m: Maybe<&2, Switch>, +ts: List<&2, Tried>, +p: Policy) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{s}:
      Nat.is_le(length(ts), Policy.switches(p))

# 4. The deferred job
# -------------------

# what the call that is out answered: the end of the turn (the job, if
# any, is done), still deferred (the next poll gap+1 ms later, never
# sooner), or a failure (retryable by the classifier; the next poll gap+1
# ms later)
type Got is Data:
  Answer{}
  Later{gap: Nat}
  Broke{retryable: Bool, gap: Nat}

# the request's job: none, or live with its failed fetches in a row and
# the ms left before its deadline
type Job is Data:
  NoJob{}
  Live{failed: Nat, left: Nat}

# what the run does next
type Act is Data:
  Send{}
  Poll{}
  Cancel{}
  Settle{}
  Quit{}

# a step: what the run does and the job after it
type Step is Data:
  Step{act: Act, job: Job}

# polls of a live job: the deadline, then the fetch failures
def live.pending(over: Bool, +left: Nat, +gap: Nat) -> Step:
  match over:
    case True{}:
      Step{Cancel{}, NoJob{}}
    case False{}:
      Step{Poll{}, Live{0n, Nat.sub(left, 1n+gap)}}

def live.failed(again: Bool, +failed: Nat, +left: Nat, +gap: Nat) -> Step:
  match again:
    case True{}:
      Step{Poll{}, Live{1n+failed, Nat.sub(left, 1n+gap)}}
    case False{}:
      Step{Cancel{}, NoJob{}}

# a request answered (`after_reply` and the poll decisions of
# `generation.rs` `classify`): fails: retry.maxRetries, the fetch failures
# a job may have in a row; budget: the ms a new job may run (its
# provider's expiry, else its requested window)
def step(+fails: Nat, +budget: Nat, +job: Job, +got: Got) -> Step:
  match job got:
    case NoJob{} Answer{}:
      Step{Settle{}, NoJob{}}
    case NoJob{} Later{gap}:
      live.pending(Nat.is_eq(budget, 0n), budget, gap)
    case NoJob{} Broke{retryable, gap}:
      match retryable:
        case True{}:
          Step{Send{}, NoJob{}}
        case False{}:
          Step{Quit{}, NoJob{}}
    case Live{failed, left} Answer{}:
      Step{Settle{}, NoJob{}}
    case Live{failed, left} Later{gap}:
      live.pending(Nat.is_eq(left, 0n), left, gap)
    case Live{failed, left} Broke{retryable, gap}:
      live.failed(Bool.and(retryable, Bool.and(Nat.is_lt(failed, fails), Nat.is_gt(left, 0n))), failed, left, gap)

def Job.live(j: Job) -> Bool:
  match j:
    case NoJob{}:
      False{}
    case Live{failed, left}:
      True{}

def Job.left(j: Job) -> Nat:
  match j:
    case NoJob{}:
      0n
    case Live{failed, left}:
      left

# sends: requests sent while a job was live; late: polls made at or after
# a job's deadline
type Tally is Data:
  Tally{sends: Nat, late: Nat}

def tally.send(a: Act, live: Bool) -> Nat:
  match a live:
    case Send{} True{}:
      1n
    case Send{} False{}:
      0n
    case Poll{} l:
      0n
    case Cancel{} l:
      0n
    case Settle{} l:
      0n
    case Quit{} l:
      0n

# a poll at a deadline already reached
def late.at(left: Nat) -> Nat:
  match left:
    case 0n:
      1n
    case 1n+k:
      0n

def tally.late(a: Act, +left: Nat, live: Bool) -> Nat:
  match a live:
    case Poll{} True{}:
      late.at(left)
    case Poll{} False{}:
      0n
    case Send{} l:
      0n
    case Cancel{} l:
      0n
    case Settle{} l:
      0n
    case Quit{} l:
      0n

def Step.act(s: Step) -> Act:
  match s:
    case Step{act, job}:
      act

def Step.job(s: Step) -> Job:
  match s:
    case Step{act, job}:
      job

def tally.add(t: Tally, +a: Act, +job: Job) -> Tally:
  match t:
    case Tally{s, l}:
      Tally{Nat.add(s, tally.send(a, Job.live(job))), Nat.add(l, tally.late(a, Job.left(job), Job.live(job)))}

def run.go(gots: List<&2, Got>, +fails: Nat, +budget: Nat, +job: Job, +t: Tally) -> Tally:
  match gots:
    case Nil{}:
      t
    case g <> rest:
      +st = step(fails, budget, job, g)
      run.go(rest, fails, budget, Step.job(st), tally.add(t, Step.act(st), job))

# a request's replies, from its first: what the run did while a job was
# live
def run(+fails: Nat, +budget: Nat, gots: List<&2, Got>) -> Tally:
  run.go(gots, fails, budget, NoJob{}, Tally{0n, 0n})

def Tally.sends(t: Tally) -> Nat:
  match t:
    case Tally{sends, late}:
      sends

def Tally.late(t: Tally) -> Nat:
  match t:
    case Tally{sends, late}:
      late

# 5. The stall
# ------------

# the idle deadline of the retry after a stream stalled under idle ms
# (`idle_after_stall`): twice the one it stalled under
def stall.next(+idle: Nat) -> Nat:
  Nat.add(idle, idle)

# 6. The idle deadline
# --------------------

# how a watched stream ends: stalled at ms after the deadline was armed,
# or closed (its provider ended it) at ms
type Idle is Data:
  IdleStall{at: Nat}
  IdleClose{at: Nat}

# the end when the next event is past the deadline (over), else on
def idle.sel(over: Bool, +stall: Idle, on: Idle) -> Idle:
  match over:
    case True{}:
      stall
    case False{}:
      on

# the events after the first, each its gap after the one before; last:
# when the event before them came. An event g ms after the one at last,
# past the deadline d, comes after the stream stalled at last + d.
def idle.go(gs: List<&2, Nat>, +d: Nat, +last: Nat) -> Idle:
  match gs:
    case Nil{}:
      IdleClose{last}
    case +g <> rest:
      idle.sel(Nat.is_gt(g, d), IdleStall{Nat.add(last, d)}, idle.go(rest, d, Nat.add(last, g)))

# a stream watched by an idle deadline of d ms (`StreamIdle::within`),
# whose events come gs ms apart, the first gs[0] ms after the deadline was
# armed; its provider ends it with its last event. A stream with no event
# never ends by itself: the deadline ends it.
def idle(gs: List<&2, Nat>, +d: Nat) -> Idle:
  match gs:
    case Nil{}:
      IdleStall{d}
    case +g <> rest:
      idle.sel(Nat.is_gt(g, d), IdleStall{d}, idle.go(rest, d, g))

# when the stream ended
def Idle.at(i: Idle) -> Nat:
  match i:
    case IdleStall{at}:
      at
    case IdleClose{at}:
      at

# the time of the last event that came before the deadline, from last
# (0 when none came)
def idle.life.sel(over: Bool, +last: Nat, on: Nat) -> Nat:
  match over:
    case True{}:
      last
    case False{}:
      on

def idle.life.go(gs: List<&2, Nat>, +d: Nat, +last: Nat) -> Nat:
  match gs:
    case Nil{}:
      last
    case +g <> rest:
      idle.life.sel(Nat.is_gt(g, d), last, idle.life.go(rest, d, Nat.add(last, g)))

def idle.life(gs: List<&2, Nat>, +d: Nat) -> Nat:
  match gs:
    case Nil{}:
      0n
    case +g <> rest:
      idle.life.sel(Nat.is_gt(g, d), 0n, idle.life.go(rest, d, g))
