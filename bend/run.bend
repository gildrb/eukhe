# run: one run of the harness (one user turn) as a state machine, after
# docs/harness.md H4. Its live phases: prepare (the request is built; a
# blocking threshold compaction may start), call (a request or a deferred
# poll is out), compact (the run waits for an overflow's or a threshold
# compaction), tools (the round's tools run). Its ends: answered (an
# answer, a control that ends the run, a queued reset), aborted, failed.
#
# Every input is the adversary's (Ev): the model's reply, how a finished
# round ends and its hash, how a compaction ended, or an abort, in any
# order, at any step. A phase reads the part of a Go it needs.
#
# The limits count down: c compactions, a retries and p polls left in the
# generation, r rounds left in the run. The Rust code counts them up; the
# bridge prints both as counts left (bend/bridge_run.bend).
#
# LAWS.bend (H4) states what must hold; PROOF.bend proves it through
# bend/proof_run.bend, and the laws of the requests a run sends (H4.7,
# Reqs at the end) through bend/proof_retry.bend. The Rust side is
# crates/eukhe-durable/src/harness/generation/decide.rs: every step below
# is one of its decisions (named at each step).

import Base

# cap: maxToolRounds; polls: MAX_POLLS; retries: retry.maxRetries;
# loop: LOOP_ROUNDS
type Cfg is Data:
  Cfg{cap: Nat, polls: Nat, retries: Nat, loop: Nat}

def Cfg.cap(c: Cfg) -> Nat:
  match c:
    case Cfg{cap, polls, retries, loop}:
      cap

def Cfg.polls(c: Cfg) -> Nat:
  match c:
    case Cfg{cap, polls, retries, loop}:
      polls

def Cfg.retries(c: Cfg) -> Nat:
  match c:
    case Cfg{cap, polls, retries, loop}:
      retries

def Cfg.loop(c: Cfg) -> Nat:
  match c:
    case Cfg{cap, polls, retries, loop}:
      loop

# why a run failed: the model (an error, or an overflow it cannot
# compact), a deferred reply past MAX_POLLS, the round cap, a loop
type Why is Data:
  Model{}
  Polls{}
  Rounds{}
  Loop{}

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
# stream repeated itself until the guard cut it, or the reply gave no
# answer
type Reply is Data:
  Text{}
  Calls{}
  Deferred{}
  Error{retryable: Bool, noted: Bool}
  Overflow{cut: Bool}

# what a message that ends the model's turn (stop reason stop, length or
# tool use) holds: tool: its stop reason is tool use; text: a text block
# that is not blank; calls: a tool call; retrying: the retry policy is on
type Ended is Data:
  Ended{tool: Bool, text: Bool, calls: Bool, retrying: Bool}

def Ended.pick(calls: Bool, text: Bool, tool: Bool, retrying: Bool) -> Reply:
  match calls text tool:
    case True{} text True{}:
      Calls{}
    case True{} text False{}:
      Text{}
    case False{} True{} tool:
      Text{}
    case False{} False{} tool:
      Error{retrying, True{}}

# the reply such a message makes (Ended::reply, docs/harness.md H4.7): its
# calls when the stop reason is tool use and it has calls, else an answer
# when it has text or a call. With no text and no call the model gave no
# answer: a noted model error, retryable when the retry policy is on
def Ended.reply(m: Ended) -> Reply:
  match m:
    case Ended{tool, text, calls, retrying}:
      Ended.pick(calls, text, tool, retrying)

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

# hash: the round's calls and results; fin: how the round ends; got: how
# the compaction ended
type Ev is Data:
  Abort{}
  Go{reply: Reply, hash: Nat, fin: Fin, got: Got}

# same: rounds in a row with hash last (0 before the first round)
type St is Data:
  St{ph: Ph, r: Nat, c: Nat, a: Nat, p: Nat, same: Nat, last: Nat}

def St.ph(s: St) -> Ph:
  match s:
    case St{ph, r, c, a, p, same, last}:
      ph

def St.r(s: St) -> Nat:
  match s:
    case St{ph, r, c, a, p, same, last}:
      r

def St.c(s: St) -> Nat:
  match s:
    case St{ph, r, c, a, p, same, last}:
      c

def St.a(s: St) -> Nat:
  match s:
    case St{ph, r, c, a, p, same, last}:
      a

def St.p(s: St) -> Nat:
  match s:
    case St{ph, r, c, a, p, same, last}:
      p

def St.same(s: St) -> Nat:
  match s:
    case St{ph, r, c, a, p, same, last}:
      same

def St.last(s: St) -> Nat:
  match s:
    case St{ph, r, c, a, p, same, last}:
      last

# a run starts preparing its first request
def init(+cfg: Cfg) -> St:
  St{Prepare{}, Nat.sub(Cfg.cap(cfg), 1n), 1n, Cfg.retries(cfg), Cfg.polls(cfg), 0n, 0n}

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

def Why.loop(w: Why) -> Bool:
  match w:
    case Model{}:
      False{}
    case Polls{}:
      False{}
    case Rounds{}:
      False{}
    case Loop{}:
      True{}

def Ph.looped(ph: Ph) -> Bool:
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
      Why.loop(why)

def looped(s: St) -> Bool:
  Ph.looped(St.ph(s))

def Why.capped(w: Why) -> Bool:
  match w:
    case Model{}:
      False{}
    case Polls{}:
      False{}
    case Rounds{}:
      True{}
    case Loop{}:
      False{}

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
    case Loop{}:
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

# the poll cap failed the run
def polled(s: St) -> Bool:
  Ph.polled(St.ph(s))

# Steps
# -----

# prepare (before_request): a blocking threshold compaction when the
# context is over it, a cut exists and the generation has not compacted;
# else the request goes out
def prepare.cut(+cfg: Cfg, cut: Bool, r: Nat, c: Nat, a: Nat, same: Nat, last: Nat) -> St:
  match cut c:
    case True{} 1n+d:
      St{Compact{False{}}, r, d, a, Cfg.polls(cfg), same, last}
    case True{} 0n:
      St{Call{}, r, 0n, a, Cfg.polls(cfg), same, last}
    case False{} c:
      St{Call{}, r, c, a, Cfg.polls(cfg), same, last}

def prepare(+cfg: Cfg, reply: Reply, r: Nat, c: Nat, a: Nat, same: Nat, last: Nat) -> St:
  match reply:
    case Overflow{cut}:
      prepare.cut(cfg, cut, r, c, a, same, last)
    case Text{}:
      St{Call{}, r, c, a, Cfg.polls(cfg), same, last}
    case Calls{}:
      St{Call{}, r, c, a, Cfg.polls(cfg), same, last}
    case Deferred{}:
      St{Call{}, r, c, a, Cfg.polls(cfg), same, last}
    case Error{retryable, noted}:
      St{Call{}, r, c, a, Cfg.polls(cfg), same, last}

# a retryable error (after_reply) retries while retries are left
def retry(+cfg: Cfg, retryable: Bool, r: Nat, c: Nat, a: Nat, p: Nat, same: Nat, last: Nat) -> St:
  match retryable a:
    case True{} 1n+b:
      St{Prepare{}, r, c, b, Cfg.polls(cfg), same, last}
    case True{} 0n:
      St{Failed{Model{}}, r, c, 0n, p, same, last}
    case False{} a:
      St{Failed{Model{}}, r, c, a, p, same, last}

# an overflow (after_reply) compacts once a generation, when a cut exists
def overflow(cut: Bool, r: Nat, c: Nat, a: Nat, p: Nat, same: Nat, last: Nat) -> St:
  match cut c:
    case True{} 1n+d:
      St{Compact{True{}}, r, d, a, p, same, last}
    case True{} 0n:
      St{Failed{Model{}}, r, 0n, a, p, same, last}
    case False{} c:
      St{Failed{Model{}}, r, c, a, p, same, last}

# a reply to a request or a poll (after_reply)
def call(+cfg: Cfg, reply: Reply, r: Nat, c: Nat, a: Nat, p: Nat, same: Nat, last: Nat) -> St:
  match reply:
    case Text{}:
      St{Answered{}, r, c, a, p, same, last}
    case Calls{}:
      St{Tools{}, r, c, a, p, same, last}
    case Deferred{}:
      match p:
        case 0n:
          St{Failed{Polls{}}, r, c, a, 0n, same, last}
        case 1n+q:
          St{Call{}, r, c, a, q, same, last}
    case Error{retryable, noted}:
      retry(cfg, retryable, r, c, a, p, same, last)
    case Overflow{cut}:
      overflow(cut, r, c, a, p, same, last)

# a compaction ends (after_compaction): the request is prepared again, or
# the run fails. An overflow's compaction must append its entry, else the
# request still overflows; a threshold one that found nothing leaves a
# request that may still fit, one that failed a context it judged too large
def compact(+cfg: Cfg, over: Bool, got: Got, r: Nat, c: Nat, a: Nat, p: Nat, same: Nat, last: Nat) -> St:
  match over got:
    case over Built{}:
      St{Prepare{}, r, c, a, Cfg.polls(cfg), same, last}
    case True{} Kept{}:
      St{Failed{Model{}}, r, c, a, p, same, last}
    case False{} Kept{}:
      St{Prepare{}, r, c, a, Cfg.polls(cfg), same, last}
    case over Broke{}:
      St{Failed{Model{}}, r, c, a, p, same, last}

# rounds in a row with hash h after a round: one more when the last
# round had it, else 1
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

# a counted round (Rounds::finish, then RoundEnd::reset): a loop fails it,
# else the cap, else a queued reset ends the run, else the next
# generation prepares with fresh limits
def round.go(+cfg: Cfg, loops: Bool, reset: Bool, r: Nat, c: Nat, a: Nat, p: Nat, same: Nat, h: Nat) -> St:
  match loops reset r:
    case True{} reset r:
      St{Failed{Loop{}}, r, c, a, p, same, h}
    case False{} reset 0n:
      St{Failed{Rounds{}}, 0n, c, a, p, same, h}
    case False{} True{} 1n+s:
      St{Answered{}, s, c, a, p, same, h}
    case False{} False{} 1n+s:
      St{Prepare{}, s, 1n, Cfg.retries(cfg), Cfg.polls(cfg), same, h}

def round(+cfg: Cfg, +h: Nat, reset: Bool, r: Nat, c: Nat, a: Nat, p: Nat, +same: Nat) -> St:
  round.go(cfg, Nat.is_ge(same, Cfg.loop(cfg)), reset, r, c, a, p, same, h)

# a round ends (RoundEnd::Stop): a control stops the run uncounted, else the
# round counts
def tools(+cfg: Cfg, +h: Nat, fin: Fin, r: Nat, c: Nat, a: Nat, p: Nat, same: Nat, +last: Nat) -> St:
  match fin:
    case Stops{}:
      St{Answered{}, r, c, a, p, same, last}
    case Goes{}:
      round(cfg, h, False{}, r, c, a, p, again(same, last, h))
    case Resets{}:
      round(cfg, h, True{}, r, c, a, p, again(same, last, h))

# one input; an abort ends a live run, an ended run stays as it is
def step.ph(+cfg: Cfg, ph: Ph, e: Ev, r: Nat, c: Nat, a: Nat, p: Nat, same: Nat, last: Nat) -> St:
  match ph e:
    case Answered{} e:
      St{Answered{}, r, c, a, p, same, last}
    case Aborted{} e:
      St{Aborted{}, r, c, a, p, same, last}
    case Failed{why} e:
      St{Failed{why}, r, c, a, p, same, last}
    case Prepare{} Abort{}:
      St{Aborted{}, r, c, a, p, same, last}
    case Call{} Abort{}:
      St{Aborted{}, r, c, a, p, same, last}
    case Compact{over} Abort{}:
      St{Aborted{}, r, c, a, p, same, last}
    case Tools{} Abort{}:
      St{Aborted{}, r, c, a, p, same, last}
    case Prepare{} Go{reply, h, fin, got}:
      prepare(cfg, reply, r, c, a, same, last)
    case Call{} Go{reply, h, fin, got}:
      call(cfg, reply, r, c, a, p, same, last)
    case Compact{over} Go{reply, h, fin, got}:
      compact(cfg, over, got, r, c, a, p, same, last)
    case Tools{} Go{reply, h, fin, got}:
      tools(cfg, h, fin, r, c, a, p, same, last)

def step(+cfg: Cfg, s: St, e: Ev) -> St:
  match s:
    case St{ph, r, c, a, p, same, last}:
      step.ph(cfg, ph, e, r, c, a, p, same, last)

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

# the hash of the round input e ends, if s is in its tools phase and the
# round counts (no control stopped it)
def counted.go(+h: Nat, fin: Fin, acc: List<&2, Nat>) -> List<&2, Nat>:
  match fin:
    case Stops{}:
      acc
    case Goes{}:
      h <> acc
    case Resets{}:
      h <> acc

def counted(ph: Ph, e: Ev, acc: List<&2, Nat>) -> List<&2, Nat>:
  match ph e:
    case Tools{} Go{reply, h, fin, got}:
      counted.go(h, fin, acc)
    case Tools{} Abort{}:
      acc
    case Prepare{} e:
      acc
    case Call{} e:
      acc
    case Compact{over} e:
      acc
    case Answered{} e:
      acc
    case Aborted{} e:
      acc
    case Failed{why} e:
      acc

def hist.go(evs: List<&2, Ev>, +cfg: Cfg, +s: St, acc: List<&2, Nat>) -> List<&2, Nat>:
  match evs:
    case Nil{}:
      acc
    case +e <> rest:
      hist.go(rest, cfg, step(cfg, s, e), counted(St.ph(s), e, acc))

# the hashes of the rounds the run made, newest first
def hist(+cfg: Cfg, evs: List<&2, Ev>) -> List<&2, Nat>:
  hist.go(evs, cfg, init(cfg), Nil{})

# the deferred replies in a row that the run's request has had, after
# input e at phase ph, from k before it; an ended run keeps its count
def defers.reply(reply: Reply, k: Nat) -> Nat:
  match reply:
    case Deferred{}:
      1n+k
    case Text{}:
      0n
    case Calls{}:
      0n
    case Error{retryable, noted}:
      0n
    case Overflow{cut}:
      0n

def defers.at(ph: Ph, e: Ev, k: Nat) -> Nat:
  match ph e:
    case Call{} Go{reply, h, fin, got}:
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

# the first k of xs are equal to x
def all_eq(k: Nat, +x: Nat, xs: List<&2, Nat>) -> Bool:
  match k xs:
    case 0n xs:
      True{}
    case 1n+j Nil{}:
      False{}
    case 1n+j y <> t:
      Bool.and(Nat.is_eq(y, x), all_eq(j, x, t))

# xs has k equal first elements
def rep(k: Nat, xs: List<&2, Nat>) -> Bool:
  match k xs:
    case 0n xs:
      True{}
    case 1n+j Nil{}:
      False{}
    case 1n+j x <> t:
      all_eq(j, x, t)

# every run has ended after this many inputs: cap generations (at least
# one), each with (retries + 2) requests (the retries, the first one and
# the one after its compaction) of 2 + polls inputs (its preparation, its
# reply and its polls), the compaction and the round's end
def bound(+cfg: Cfg) -> Nat:
  Nat.mul(Nat.max(Cfg.cap(cfg), 1n), 2n+Nat.mul(2n+Cfg.retries(cfg), 2n+Cfg.polls(cfg)))

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
    case Text{}:
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
    case Call{} Go{reply, h, fin, got}:
      Reqs.reply(reply, ctx, n, note, log)
    case Call{} Abort{}:
      Reqs{ctx, n, note, log}
    case Compact{over} Go{reply, h, fin, got}:
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
