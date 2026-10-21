# run: one run of the harness (one user turn) as a state machine, after
# docs/harness.md H4. Its live phases: prepare (the request is built; a
# blocking threshold compaction may start), call (a request or a deferred
# poll is out), compact (the run waits for an overflow's or a threshold
# compaction), tools (the round's tools run). Its ends: answered (an
# answer, a control that ends the run, a queued reset), aborted, failed.
#
# Every input is the adversary's (Ev): the model's reply, how a finished
# round ends, how a compaction ended, or an abort, in any order, at any
# step. A phase reads the part of a Go it needs.
#
# The limits count down: c compactions, a retries and n notes left in the
# generation, p ms left of the deferred job's time (a poll spends 1 ms),
# r rounds left in the run. A retry spends a retry; a retry after a
# noted reply spends a note. The Rust code counts them up; the bridge
# prints both as counts left (bend/bridge_run.bend).
# A row of the same calls with the same results gets a recovery
# (Recoveries, H4.8), so the run has no loop guard.
#
# LAWS.bend (H4) states what must hold; PROOF.bend proves it through
# bend/proof_run.bend, and the laws of the requests a run sends (H4.7,
# Reqs at the end) through bend/proof_retry.bend. The Rust side is
# crates/eukhe-durable/src/harness/generation/decide.rs: every step below
# is one of its decisions (named at each step).

import Base

# cap: maxToolRounds; polls: the ms a deferred job may run
# (`Limits::max_wait`); retries: retry.maxRetries;
# notes: MAX_NOTES (the noted retries of a generation)
type Cfg is Data:
  Cfg{cap: Nat, polls: Nat, retries: Nat, notes: Nat}

def Cfg.cap(c: Cfg) -> Nat:
  match c:
    case Cfg{cap, polls, retries, notes}:
      cap

def Cfg.polls(c: Cfg) -> Nat:
  match c:
    case Cfg{cap, polls, retries, notes}:
      polls

def Cfg.retries(c: Cfg) -> Nat:
  match c:
    case Cfg{cap, polls, retries, notes}:
      retries

def Cfg.notes(c: Cfg) -> Nat:
  match c:
    case Cfg{cap, polls, retries, notes}:
      notes

# why a run failed: the model (an error, a noted reply past MAX_NOTES, or
# an overflow it cannot compact), a deferred reply at its job's deadline,
# the round cap
type Why is Data:
  Model{}
  Polls{}
  Rounds{}

# over: the compaction is an overflow's, else a blocking threshold one
type Ph is Data:
  Prepare{}
  Call{}
  Compact{over: Bool}
  Tools{}
  Answered{}
  Aborted{}
  Failed{why: Why}

# how a model call ended. At prepare, an overflow is a context over the
# threshold; cut: compaction finds a cut. A message that ends the model's
# turn makes Text, Calls or Error through Ended.reply. noted: the reply
# was cut, so its retry must not send the request again (H4.7): the
# stream repeated itself until the guard cut it, the reply gave no
# answer, or a recovery (Act.reply)
type Reply is Data:
  Plain{}
  Calls{}
  Deferred{}
  Error{retryable: Bool, noted: Bool}
  Overflow{cut: Bool}

# what a message that ends the model's turn (any stop reason) holds:
# text: a text block that is not blank; calls: a tool call
type Ended is Data:
  Ended{text: Bool, calls: Bool}

def Ended.text(text: Bool) -> Reply:
  match text:
    case True{}:
      Plain{}
    case False{}:
      Error{False{}, True{}}

def Ended.pick(calls: Bool, text: Bool) -> Reply:
  match calls:
    case True{}:
      Calls{}
    case False{}:
      Ended.text(text)

# the reply such a message makes (Ended::reply, docs/harness.md H4.7): its
# calls when it has a tool call, whatever its stop reason (vLLM,
# llama.cpp and Ollama send the stop reason stop with tool calls); else
# an answer when it has text. With no text and no call the model gave no
# answer: a noted error
def Ended.reply(m: Ended) -> Reply:
  match m:
    case Ended{text, calls}:
      Ended.pick(calls, text)

# how a compaction ended: it appended its entry, it found nothing to
# compact (or declined), or it failed (or was aborted or orphaned)
type Got is Data:
  Built{}
  Kept{}
  Broke{}

# how a round ends: it goes on to the next generation, a control ends the
# run (terminate, handoff), or a queued reset at its boundary ends it
type Fin is Data:
  Goes{}
  Stops{}
  Resets{}

# fin: how the round ends; got: how the compaction ended
type Ev is Data:
  Abort{}
  Go{reply: Reply, fin: Fin, got: Got}

type St is Data:
  St{ph: Ph, r: Nat, c: Nat, a: Nat, n: Nat, p: Nat}

def St.ph(s: St) -> Ph:
  match s:
    case St{ph, r, c, a, n, p}:
      ph

def St.r(s: St) -> Nat:
  match s:
    case St{ph, r, c, a, n, p}:
      r

def St.c(s: St) -> Nat:
  match s:
    case St{ph, r, c, a, n, p}:
      c

def St.a(s: St) -> Nat:
  match s:
    case St{ph, r, c, a, n, p}:
      a

def St.n(s: St) -> Nat:
  match s:
    case St{ph, r, c, a, n, p}:
      n

def St.p(s: St) -> Nat:
  match s:
    case St{ph, r, c, a, n, p}:
      p

# a run starts preparing its first request
def init(+cfg: Cfg) -> St:
  St{Prepare{}, Nat.sub(Cfg.cap(cfg), 1n), 1n, Cfg.retries(cfg), Cfg.notes(cfg), Cfg.polls(cfg)}

def Ph.done(ph: Ph) -> Bool:
  match ph:
    case Prepare{}:
      False{}
    case Call{}:
      False{}
    case Compact{over}:
      False{}
    case Tools{}:
      False{}
    case Answered{}:
      True{}
    case Aborted{}:
      True{}
    case Failed{why}:
      True{}

def done(s: St) -> Bool:
  Ph.done(St.ph(s))

def Ph.failed(ph: Ph) -> Bool:
  match ph:
    case Prepare{}:
      False{}
    case Call{}:
      False{}
    case Compact{over}:
      False{}
    case Tools{}:
      False{}
    case Answered{}:
      False{}
    case Aborted{}:
      False{}
    case Failed{why}:
      True{}

def failed(s: St) -> Bool:
  Ph.failed(St.ph(s))

def Why.capped(w: Why) -> Bool:
  match w:
    case Model{}:
      False{}
    case Polls{}:
      False{}
    case Rounds{}:
      True{}

def Ph.capped(ph: Ph) -> Bool:
  match ph:
    case Prepare{}:
      False{}
    case Call{}:
      False{}
    case Compact{over}:
      False{}
    case Tools{}:
      False{}
    case Answered{}:
      False{}
    case Aborted{}:
      False{}
    case Failed{why}:
      Why.capped(why)

# the round cap failed the run
def capped(s: St) -> Bool:
  Ph.capped(St.ph(s))

def Why.polled(w: Why) -> Bool:
  match w:
    case Model{}:
      False{}
    case Polls{}:
      True{}
    case Rounds{}:
      False{}

def Ph.polled(ph: Ph) -> Bool:
  match ph:
    case Prepare{}:
      False{}
    case Call{}:
      False{}
    case Compact{over}:
      False{}
    case Tools{}:
      False{}
    case Answered{}:
      False{}
    case Aborted{}:
      False{}
    case Failed{why}:
      Why.polled(why)

# the job's deadline failed the run
def polled(s: St) -> Bool:
  Ph.polled(St.ph(s))

# Steps
# -----

# prepare (before_request): a blocking threshold compaction when the
# context is over it, a cut exists and the generation has not compacted;
# else the request goes out
def prepare.cut(+cfg: Cfg, cut: Bool, r: Nat, c: Nat, a: Nat, n: Nat) -> St:
  match cut c:
    case True{} 1n+d:
      St{Compact{False{}}, r, d, a, n, Cfg.polls(cfg)}
    case True{} 0n:
      St{Call{}, r, 0n, a, n, Cfg.polls(cfg)}
    case False{} c:
      St{Call{}, r, c, a, n, Cfg.polls(cfg)}

def prepare(+cfg: Cfg, reply: Reply, r: Nat, c: Nat, a: Nat, n: Nat) -> St:
  match reply:
    case Overflow{cut}:
      prepare.cut(cfg, cut, r, c, a, n)
    case Plain{}:
      St{Call{}, r, c, a, n, Cfg.polls(cfg)}
    case Calls{}:
      St{Call{}, r, c, a, n, Cfg.polls(cfg)}
    case Deferred{}:
      St{Call{}, r, c, a, n, Cfg.polls(cfg)}
    case Error{retryable, noted}:
      St{Call{}, r, c, a, n, Cfg.polls(cfg)}

# an error that is not noted (after_reply) retries when it is retryable
# and retries are left; it spends a retry, never a note
def retry(+cfg: Cfg, retryable: Bool, r: Nat, c: Nat, a: Nat, n: Nat, p: Nat) -> St:
  match retryable a:
    case True{} 1n+b:
      St{Prepare{}, r, c, b, n, Cfg.polls(cfg)}
    case True{} 0n:
      St{Failed{Model{}}, r, c, 0n, n, p}
    case False{} a:
      St{Failed{Model{}}, r, c, a, n, p}

# a noted reply (after_reply, retry_note) retries with a note while notes
# are left, retryable or not; it spends a note, never a retry
def note(+cfg: Cfg, r: Nat, c: Nat, a: Nat, n: Nat, p: Nat) -> St:
  match n:
    case 1n+m:
      St{Prepare{}, r, c, a, m, Cfg.polls(cfg)}
    case 0n:
      St{Failed{Model{}}, r, c, a, 0n, p}

def error(+cfg: Cfg, retryable: Bool, noted: Bool, r: Nat, c: Nat, a: Nat, n: Nat, p: Nat) -> St:
  match noted:
    case True{}:
      note(cfg, r, c, a, n, p)
    case False{}:
      retry(cfg, retryable, r, c, a, n, p)

# an overflow (after_reply) compacts once a generation, when a cut exists
def overflow(cut: Bool, r: Nat, c: Nat, a: Nat, n: Nat, p: Nat) -> St:
  match cut c:
    case True{} 1n+d:
      St{Compact{True{}}, r, d, a, n, p}
    case True{} 0n:
      St{Failed{Model{}}, r, 0n, a, n, p}
    case False{} c:
      St{Failed{Model{}}, r, c, a, n, p}

# a reply to a request or a poll (after_reply)
def call(+cfg: Cfg, reply: Reply, r: Nat, c: Nat, a: Nat, n: Nat, p: Nat) -> St:
  match reply:
    case Plain{}:
      St{Answered{}, r, c, a, n, p}
    case Calls{}:
      St{Tools{}, r, c, a, n, p}
    case Deferred{}:
      match p:
        case 0n:
          St{Failed{Polls{}}, r, c, a, n, 0n}
        case 1n+q:
          St{Call{}, r, c, a, n, q}
    case Error{retryable, noted}:
      error(cfg, retryable, noted, r, c, a, n, p)
    case Overflow{cut}:
      overflow(cut, r, c, a, n, p)

# a compaction ends (after_compaction): the request is prepared again, or
# the run fails. An overflow's compaction must append its entry, else the
# request still overflows; a threshold one that found nothing leaves a
# request that may still fit, one that failed a context it judged too large
def compact(+cfg: Cfg, over: Bool, got: Got, r: Nat, c: Nat, a: Nat, n: Nat, p: Nat) -> St:
  match over got:
    case over Built{}:
      St{Prepare{}, r, c, a, n, Cfg.polls(cfg)}
    case True{} Kept{}:
      St{Failed{Model{}}, r, c, a, n, p}
    case False{} Kept{}:
      St{Prepare{}, r, c, a, n, Cfg.polls(cfg)}
    case over Broke{}:
      St{Failed{Model{}}, r, c, a, n, p}

# rounds in a row with hash h after a round: one more when the last
# round had it, else 1 (the recoveries count their rows with it)
def again.eq(eq: Bool, k: Nat) -> Nat:
  match eq:
    case True{}:
      2n+k
    case False{}:
      1n

def again(same: Nat, +last: Nat, +h: Nat) -> Nat:
  match same:
    case 0n:
      1n
    case 1n+k:
      again.eq(Nat.is_eq(last, h), k)

# a counted round (Rounds::finish, then RoundEnd::reset): the cap fails
# it, else a queued reset ends the run, else the next generation prepares
# with fresh limits
def round(+cfg: Cfg, reset: Bool, r: Nat, c: Nat, a: Nat, n: Nat, p: Nat) -> St:
  match reset r:
    case reset 0n:
      St{Failed{Rounds{}}, 0n, c, a, n, p}
    case True{} 1n+s:
      St{Answered{}, s, c, a, n, p}
    case False{} 1n+s:
      St{Prepare{}, s, 1n, Cfg.retries(cfg), Cfg.notes(cfg), Cfg.polls(cfg)}

# a round ends (RoundEnd::Stop): a control stops the run uncounted, else the
# round counts
def tools(+cfg: Cfg, fin: Fin, r: Nat, c: Nat, a: Nat, n: Nat, p: Nat) -> St:
  match fin:
    case Stops{}:
      St{Answered{}, r, c, a, n, p}
    case Goes{}:
      round(cfg, False{}, r, c, a, n, p)
    case Resets{}:
      round(cfg, True{}, r, c, a, n, p)

# one input; an abort ends a live run, an ended run stays as it is
def step.ph(+cfg: Cfg, ph: Ph, e: Ev, r: Nat, c: Nat, a: Nat, n: Nat, p: Nat) -> St:
  match ph e:
    case Answered{} e:
      St{Answered{}, r, c, a, n, p}
    case Aborted{} e:
      St{Aborted{}, r, c, a, n, p}
    case Failed{why} e:
      St{Failed{why}, r, c, a, n, p}
    case Prepare{} Abort{}:
      St{Aborted{}, r, c, a, n, p}
    case Call{} Abort{}:
      St{Aborted{}, r, c, a, n, p}
    case Compact{over} Abort{}:
      St{Aborted{}, r, c, a, n, p}
    case Tools{} Abort{}:
      St{Aborted{}, r, c, a, n, p}
    case Prepare{} Go{reply, fin, got}:
      prepare(cfg, reply, r, c, a, n)
    case Call{} Go{reply, fin, got}:
      call(cfg, reply, r, c, a, n, p)
    case Compact{over} Go{reply, fin, got}:
      compact(cfg, over, got, r, c, a, n, p)
    case Tools{} Go{reply, fin, got}:
      tools(cfg, fin, r, c, a, n, p)

def step(+cfg: Cfg, s: St, e: Ev) -> St:
  match s:
    case St{ph, r, c, a, n, p}:
      step.ph(cfg, ph, e, r, c, a, n, p)

def run.go(evs: List<&2, Ev>, +cfg: Cfg, s: St) -> St:
  match evs:
    case Nil{}:
      s
    case e <> rest:
      run.go(rest, cfg, step(cfg, s, e))

# the run after evs
def run(+cfg: Cfg, evs: List<&2, Ev>) -> St:
  run.go(evs, cfg, init(cfg))

# What the laws read
# ------------------

# the counted rounds after input e, from k before it: one more if s is
# in its tools phase and the round counts (no control stopped it)
def counted.go(fin: Fin, k: Nat) -> Nat:
  match fin:
    case Stops{}:
      k
    case Goes{}:
      1n+k
    case Resets{}:
      1n+k

def counted(ph: Ph, e: Ev, k: Nat) -> Nat:
  match ph e:
    case Tools{} Go{reply, fin, got}:
      counted.go(fin, k)
    case Tools{} Abort{}:
      k
    case Prepare{} e:
      k
    case Call{} e:
      k
    case Compact{over} e:
      k
    case Answered{} e:
      k
    case Aborted{} e:
      k
    case Failed{why} e:
      k

def rounds.go(evs: List<&2, Ev>, +cfg: Cfg, +s: St, k: Nat) -> Nat:
  match evs:
    case Nil{}:
      k
    case +e <> rest:
      rounds.go(rest, cfg, step(cfg, s, e), counted(St.ph(s), e, k))

# the counted rounds the run made
def rounds(+cfg: Cfg, evs: List<&2, Ev>) -> Nat:
  rounds.go(evs, cfg, init(cfg), 0n)

# the deferred replies in a row that the run's request has had, after
# input e at phase ph, from k before it; an ended run keeps its count
def defers.reply(reply: Reply, k: Nat) -> Nat:
  match reply:
    case Deferred{}:
      1n+k
    case Plain{}:
      0n
    case Calls{}:
      0n
    case Error{retryable, noted}:
      0n
    case Overflow{cut}:
      0n

def defers.at(ph: Ph, e: Ev, k: Nat) -> Nat:
  match ph e:
    case Call{} Go{reply, fin, got}:
      defers.reply(reply, k)
    case Call{} Abort{}:
      0n
    case Prepare{} e:
      0n
    case Compact{over} e:
      0n
    case Tools{} e:
      0n
    case Answered{} e:
      k
    case Aborted{} e:
      k
    case Failed{why} e:
      k

def defers.go(evs: List<&2, Ev>, +cfg: Cfg, +s: St, k: Nat) -> Nat:
  match evs:
    case Nil{}:
      k
    case +e <> rest:
      defers.go(rest, cfg, step(cfg, s, e), defers.at(St.ph(s), e, k))

# the deferred replies in a row the run's last request had
def defers(+cfg: Cfg, evs: List<&2, Ev>) -> Nat:
  defers.go(evs, cfg, init(cfg), 0n)

# every run has ended after this many inputs: cap generations (at least
# one), each with (retries + notes + 2) requests (the retries, the noted
# retries, the first one and the one after its compaction) of 2 + polls
# inputs (its preparation, its reply and its polls), the compaction and
# the round's end
def bound(+cfg: Cfg) -> Nat:
  Nat.mul(Nat.max(Cfg.cap(cfg), 1n), 2n+Nat.mul(2n+Nat.add(Cfg.retries(cfg), Cfg.notes(cfg)), 2n+Cfg.polls(cfg)))

# The requests
# ------------
# docs/harness.md H4.7. The model decodes the same request the same way
# (a greedy model always does), so a retry after a noted reply (a stream
# cut as repeating, a reply with no answer) must not send that request
# again. Its request ends with a harness note that names the retry's
# attempt and what went wrong; a retry after any other error sends the
# request it retries, note and all. The note goes out with the request
# only: the run never logs it (generation.rs, `request`).
#
# A request is its logged context and its note. The logged context only
# grows (a counted round adds its calls and results, a compaction its
# entry), so a version number names it: two contexts of one run are the
# same exactly when their versions are.

# ctx: the version of the logged context the request sends; note: the
# attempt its note names, 0 for no note
type Req is Data:
  Req{ctx: Nat, note: Nat}

def Req.ctx(q: Req) -> Nat:
  match q:
    case Req{ctx, note}:
      ctx

def Req.note(q: Req) -> Nat:
  match q:
    case Req{ctx, note}:
      note

# a and b are the same request
def Req.is(a: Req, b: Req) -> Bool:
  match a b:
    case Req{c, m} Req{d, k}:
      Bool.and(Nat.is_eq(c, d), Nat.is_eq(m, k))

# what the run did with a request: it sent it, or the reply to it was
# noted (the request was cut)
type Sent is Data:
  Sent{q: Req}
  Cut{q: Req}

# the requests of a run: the version of its logged context, the attempt
# of its generation (1 for the first request, as Counts::attempt), the
# note its next request carries, and what it sent and cut, newest first
type Reqs is Data:
  Reqs{ctx: Nat, n: Nat, note: Nat, log: List<&2, Sent>}

def Reqs.ctx(t: Reqs) -> Nat:
  match t:
    case Reqs{ctx, n, note, log}:
      ctx

def Reqs.n(t: Reqs) -> Nat:
  match t:
    case Reqs{ctx, n, note, log}:
      n

def Reqs.note(t: Reqs) -> Nat:
  match t:
    case Reqs{ctx, n, note, log}:
      note

def Reqs.log(t: Reqs) -> List<&2, Sent>:
  match t:
    case Reqs{ctx, n, note, log}:
      log

# a run starts with context 0, at attempt 1, with no note
def Reqs.init() -> Reqs:
  Reqs{0n, 1n, 0n, Nil{}}

# preparation that ends in a call sends the request
def Reqs.prepared(pa: Ph, +ctx: Nat, n: Nat, +note: Nat, log: List<&2, Sent>) -> Reqs:
  match pa:
    case Call{}:
      Reqs{ctx, n, note, Sent{Req{ctx, note}} <> log}
    case Prepare{}:
      Reqs{ctx, n, note, log}
    case Compact{over}:
      Reqs{ctx, n, note, log}
    case Tools{}:
      Reqs{ctx, n, note, log}
    case Answered{}:
      Reqs{ctx, n, note, log}
    case Aborted{}:
      Reqs{ctx, n, note, log}
    case Failed{why}:
      Reqs{ctx, n, note, log}

# an error counts an attempt (retry_note): a noted one cuts the request,
# and the retry's note names the retry's attempt; any other leaves the
# note as it is, so the retry sends the request it retries
def Reqs.error(noted: Bool, +ctx: Nat, +n: Nat, note: Nat, log: List<&2, Sent>) -> Reqs:
  match noted:
    case True{}:
      Reqs{ctx, 1n+n, 1n+n, Cut{Req{ctx, note}} <> log}
    case False{}:
      Reqs{ctx, 1n+n, note, log}

def Reqs.reply(reply: Reply, +ctx: Nat, +n: Nat, note: Nat, log: List<&2, Sent>) -> Reqs:
  match reply:
    case Error{retryable, noted}:
      Reqs.error(noted, ctx, n, note, log)
    case Plain{}:
      Reqs{ctx, n, note, log}
    case Calls{}:
      Reqs{ctx, n, note, log}
    case Deferred{}:
      Reqs{ctx, n, note, log}
    case Overflow{cut}:
      Reqs{ctx, n, note, log}

# a compaction that appended its entry grows the context
def Reqs.compacted(got: Got, ctx: Nat, n: Nat, note: Nat, log: List<&2, Sent>) -> Reqs:
  match got:
    case Built{}:
      Reqs{1n+ctx, n, note, log}
    case Kept{}:
      Reqs{ctx, n, note, log}
    case Broke{}:
      Reqs{ctx, n, note, log}

# a round that goes on to the next generation grows the context; that
# generation starts at attempt 1, with no note
def Reqs.rounded(pa: Ph, ctx: Nat, n: Nat, note: Nat, log: List<&2, Sent>) -> Reqs:
  match pa:
    case Prepare{}:
      Reqs{1n+ctx, 1n, 0n, log}
    case Call{}:
      Reqs{ctx, n, note, log}
    case Compact{over}:
      Reqs{ctx, n, note, log}
    case Tools{}:
      Reqs{ctx, n, note, log}
    case Answered{}:
      Reqs{ctx, n, note, log}
    case Aborted{}:
      Reqs{ctx, n, note, log}
    case Failed{why}:
      Reqs{ctx, n, note, log}

def Reqs.go(pb: Ph, e: Ev, pa: Ph, +ctx: Nat, +n: Nat, +note: Nat, log: List<&2, Sent>) -> Reqs:
  match pb e:
    case Prepare{} e:
      Reqs.prepared(pa, ctx, n, note, log)
    case Call{} Go{reply, fin, got}:
      Reqs.reply(reply, ctx, n, note, log)
    case Call{} Abort{}:
      Reqs{ctx, n, note, log}
    case Compact{over} Go{reply, fin, got}:
      Reqs.compacted(got, ctx, n, note, log)
    case Compact{over} Abort{}:
      Reqs{ctx, n, note, log}
    case Tools{} e:
      Reqs.rounded(pa, ctx, n, note, log)
    case Answered{} e:
      Reqs{ctx, n, note, log}
    case Aborted{} e:
      Reqs{ctx, n, note, log}
    case Failed{why} e:
      Reqs{ctx, n, note, log}

# the requests after input e takes the run from phase pb to phase pa
def Reqs.step(pb: Ph, e: Ev, pa: Ph, t: Reqs) -> Reqs:
  match t:
    case Reqs{ctx, n, note, log}:
      Reqs.go(pb, e, pa, ctx, n, note, log)

def reqs.go(evs: List<&2, Ev>, +cfg: Cfg, +s: St, t: Reqs) -> Reqs:
  match evs:
    case Nil{}:
      t
    case +e <> rest:
      +s2 = step(cfg, s, e)
      reqs.go(rest, cfg, s2, Reqs.step(St.ph(s), e, St.ph(s2), t))

# the requests of the run after evs
def reqs(+cfg: Cfg, evs: List<&2, Ev>) -> Reqs:
  reqs.go(evs, cfg, init(cfg), Reqs.init())

# a request of xs was cut and is q
def cut_in(+q: Req, xs: List<&2, Sent>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Sent{p} <> t:
      cut_in(q, t)
    case Cut{p} <> t:
      Bool.or(Req.is(p, q), cut_in(q, t))

# no request of xs (newest first) was sent after a request equal to it
# was cut
def fresh(+xs: List<&2, Sent>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Sent{q} <> t:
      Bool.and(Bool.not(cut_in(q, t)), fresh(t))
    case Cut{q} <> t:
      fresh(t)

# a line the model reads in a request: its logged context, or the
# harness note that names an attempt
type Line is Data:
  Context{ctx: Nat}
  Note{attempt: Nat}

def note.lines(note: Nat) -> List<&2, Line>:
  match note:
    case 0n:
      Nil{}
    case 1n+k:
      Note{1n+k} <> Nil{}

# what the model reads of a request: its context, then its note
def Req.lines(q: Req) -> List<&2, Line>:
  match q:
    case Req{ctx, note}:
      Context{ctx} <> note.lines(note)

# what the run logs of the lines it sends: their context. It commits the
# context's entries and the replies, never a line it adds to a request
def logged(ls: List<&2, Line>) -> List<&2, Line>:
  match ls:
    case Nil{}:
      Nil{}
    case Context{c} <> t:
      Context{c} <> logged(t)
    case Note{a} <> t:
      logged(t)

# Recoveries
# ----------
# docs/harness.md H4.8. Three replies a weaker model gives when it is
# stuck get a recovery, each with a cap: a length stop while it is still
# reasoning (no text and no tool call), tool calls that it wrote as text
# (markup in the answer), and the same tool calls (names and arguments)
# round after round. A recovery turns the reply into one that the steps
# above already read (Act.reply): a noted error, whose retry ends its
# request with a note of the recovery (H4.7), calls that run, or an
# answer. Thus every law above holds for a run with the recoveries too:
# those laws hold for every reply. The Rust side is decide.rs `recover`.

# long: LENGTH_NOTES (3), leak: LEAK_NOTES (2), redirect:
# REDIRECT_NOTES (2), repeat: REPEAT_CALLS (5)
type RCfg is Data:
  RCfg{long: Nat, leak: Nat, redirect: Nat, repeat: Nat}

def RCfg.long(c: RCfg) -> Nat:
  match c:
    case RCfg{long, leak, redirect, repeat}:
      long

def RCfg.leak(c: RCfg) -> Nat:
  match c:
    case RCfg{long, leak, redirect, repeat}:
      leak

def RCfg.redirect(c: RCfg) -> Nat:
  match c:
    case RCfg{long, leak, redirect, repeat}:
      redirect

def RCfg.repeat(c: RCfg) -> Nat:
  match c:
    case RCfg{long, leak, redirect, repeat}:
      repeat

# a < b
def below(a: Nat, b: Nat) -> Bool:
  match a b:
    case 0n 0n:
      False{}
    case 0n 1n+q:
      True{}
    case 1n+p 0n:
      False{}
    case 1n+p 1n+q:
      below(p, q)

# the recovery that the note of the next request counts: none (no note,
# or the note after a stream cut as repeating or a reply with no
# answer), a length stop, a leaked call, a repeated call
type Rk is Data:
  Free{}
  Longs{}
  Leaks{}
  Loops{}

# what a reply holds, as the recoveries read it. Long: a length stop with
# no text and no tool call. Leak: tool-call markup in its text and no
# tool call; rebuilt: every leaked call parsed and names a tool that the
# request offered, so the calls are rebuilt, as Ran. Ran: tool calls
# (any stop reason), h the hash of their names and arguments; kept: when
# they run, their results are the results of the last round (a result
# that changes is progress, as a job that a call polls, so it is no
# repeat). Noted: another noted reply (a stream cut as repeating, no
# answer). Said: a user message joins the context (a steer, the user's
# next turn): the user changed the context, so no call repeats across it.
# Answer: an answer with no tool call. Other: any other reply (an error
# that is not noted, deferred, an overflow)
type Out is Data:
  Long{}
  Leak{rebuilt: Bool, h: Nat, kept: Bool}
  Ran{h: Nat, kept: Bool}
  Noted{}
  Said{}
  Answer{}
  Other{}

# k and row: the recovery that the note of the next request counts and
# the notes of it in a row; same: the rounds in a row that the run ran
# with the calls of hash last and the same results (0: none)
type Rec is Data:
  Rec{k: Rk, row: Nat, same: Nat, last: Nat}

# the rounds in a row after a round that would make m: m when its
# results are those of the last round, else it starts a new row
def ran.same(kept: Bool, m: Nat) -> Nat:
  match kept:
    case True{}:
      m
    case False{}:
      1n

def Rec.same(r: Rec) -> Nat:
  match r:
    case Rec{k, row, same, last}:
      same

# what a recovery does with a reply. Pass: no recovery; the reply goes on
# as it is. Exec: its calls run. Redo: a noted error, so a retry whose
# note names the recovery. Stand: the reply answers as text. Quit: the
# cap is reached; the run fails on the model
type Act is Data:
  Pass{}
  Exec{}
  Redo{}
  Stand{}
  Quit{}

# the reply that the steps above read; pass: the reply as Ended.reply
# made it
def Act.reply(a: Act, pass: Reply) -> Reply:
  match a:
    case Pass{}:
      pass
    case Exec{}:
      Calls{}
    case Redo{}:
      Error{False{}, True{}}
    case Stand{}:
      Plain{}
    case Quit{}:
      Error{False{}, False{}}

# an act and the recoveries after it
type Dec is Data:
  Dec{act: Act, r: Rec}

def Dec.act(d: Dec) -> Act:
  match d:
    case Dec{act, r}:
      act

def Dec.r(d: Dec) -> Rec:
  match d:
    case Dec{act, r}:
      r

# the notes of each recovery in a row that the next request's note makes:
# its row when it counts that recovery, else 0
def Rk.longs(k: Rk, row: Nat) -> Nat:
  match k:
    case Free{}:
      0n
    case Longs{}:
      row
    case Leaks{}:
      0n
    case Loops{}:
      0n

def Rk.leaks(k: Rk, row: Nat) -> Nat:
  match k:
    case Free{}:
      0n
    case Longs{}:
      0n
    case Leaks{}:
      row
    case Loops{}:
      0n

def Rk.loops(k: Rk, row: Nat) -> Nat:
  match k:
    case Free{}:
      0n
    case Longs{}:
      0n
    case Leaks{}:
      0n
    case Loops{}:
      row

# a length stop with no answer: under the cap (n notes in a row) a retry
# with the next length note; at the cap the run fails
def rec.long(under: Bool, +n: Nat, +same: Nat, +last: Nat, r: Rec) -> Dec:
  match under:
    case True{}:
      Dec{Redo{}, Rec{Longs{}, 1n+n, same, last}}
    case False{}:
      Dec{Quit{}, r}

# leaked calls that were not rebuilt: under the cap a retry with the next
# leak note; at the cap the reply answers as text
def rec.leak(under: Bool, +n: Nat, +same: Nat, +last: Nat, r: Rec) -> Dec:
  match under:
    case True{}:
      Dec{Redo{}, Rec{Leaks{}, 1n+n, same, last}}
    case False{}:
      Dec{Stand{}, r}

# tool calls that would make m rounds in a row: below the repeat cap they
# run (kept: their results are the last round's), and the next generation
# starts with no note; else they do not run: under the cap a retry with
# the next redirect note, at it the run fails
def rec.ran(fresh: Bool, under: Bool, kept: Bool, +m: Nat, +h: Nat, +n: Nat, +same: Nat, +last: Nat, r: Rec) -> Dec:
  match fresh under:
    case True{} under:
      Dec{Exec{}, Rec{Free{}, 0n, ran.same(kept, m), h}}
    case False{} True{}:
      Dec{Redo{}, Rec{Loops{}, 1n+n, same, last}}
    case False{} False{}:
      Dec{Quit{}, r}

def rec.go(+rc: RCfg, o: Out, +k: Rk, +row: Nat, +same: Nat, +last: Nat) -> Dec:
  match o:
    case Long{}:
      rec.long(below(Rk.longs(k, row), RCfg.long(rc)), Rk.longs(k, row), same, last, Rec{k, row, same, last})
    case Leak{rebuilt, +h, kept}:
      match rebuilt:
        case True{}:
          rec.ran(below(again(same, last, h), RCfg.repeat(rc)), below(Rk.loops(k, row), RCfg.redirect(rc)), kept, again(same, last, h), h, Rk.loops(k, row), same, last, Rec{k, row, same, last})
        case False{}:
          rec.leak(below(Rk.leaks(k, row), RCfg.leak(rc)), Rk.leaks(k, row), same, last, Rec{k, row, same, last})
    case Ran{+h, kept}:
      rec.ran(below(again(same, last, h), RCfg.repeat(rc)), below(Rk.loops(k, row), RCfg.redirect(rc)), kept, again(same, last, h), h, Rk.loops(k, row), same, last, Rec{k, row, same, last})
    case Noted{}:
      Dec{Pass{}, Rec{Free{}, 0n, same, last}}
    case Said{}:
      Dec{Pass{}, Rec{k, row, 0n, last}}
    case Answer{}:
      Dec{Pass{}, Rec{Free{}, 0n, 0n, last}}
    case Other{}:
      Dec{Pass{}, Rec{k, row, same, last}}

# the recovery of one reply (decide.rs `recover`; a Noted, Said, Answer
# or Other reply is `retry_note` and the context alone)
def Rec.step(+rc: RCfg, o: Out, r: Rec) -> Dec:
  match r:
    case Rec{k, row, same, last}:
      rec.go(rc, o, k, row, same, last)

# a run starts with no note and no round
def Rec.init() -> Rec:
  Rec{Free{}, 0n, 0n, 0n}

def Rec.go(os: List<&2, Out>, +rc: RCfg, r: Rec) -> Rec:
  match os:
    case Nil{}:
      r
    case o <> rest:
      Rec.go(rest, rc, Dec.r(Rec.step(rc, o, r)))

# the recoveries after the replies os
def Rec.run(+rc: RCfg, os: List<&2, Out>) -> Rec:
  Rec.go(os, rc, Rec.init())

# the row of the next note is at most the cap of its recovery
def Rk.capped(+rc: RCfg, k: Rk, row: Nat) -> Bool:
  match k:
    case Free{}:
      True{}
    case Longs{}:
      below(row, 1n+RCfg.long(rc))
    case Leaks{}:
      below(row, 1n+RCfg.leak(rc))
    case Loops{}:
      below(row, 1n+RCfg.redirect(rc))

def Rec.capped(+rc: RCfg, r: Rec) -> Bool:
  match r:
    case Rec{k, row, same, last}:
      Rk.capped(rc, k, row)

# the act runs tool calls
def Act.runs(a: Act) -> Bool:
  match a:
    case Pass{}:
      False{}
    case Exec{}:
      True{}
    case Redo{}:
      False{}
    case Stand{}:
      False{}
    case Quit{}:
      False{}

# the reply is stuck: a length stop with no answer, leaked tool calls,
# tool calls (which may repeat)
def Out.stuck(o: Out) -> Bool:
  match o:
    case Long{}:
      True{}
    case Leak{rebuilt, h, kept}:
      True{}
    case Ran{h, kept}:
      True{}
    case Noted{}:
      False{}
    case Said{}:
      False{}
    case Answer{}:
      False{}
    case Other{}:
      False{}

# the act does something about the reply: it runs calls that are no
# repeat, retries with a note (a new request, H4.7), answers, or ends the
# run; only Pass leaves the reply as it is
def Act.helps(a: Act) -> Bool:
  match a:
    case Pass{}:
      False{}
    case Exec{}:
      True{}
    case Redo{}:
      True{}
    case Stand{}:
      True{}
    case Quit{}:
      True{}
