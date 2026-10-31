# run: the run's configuration, inputs (Reply, Got, Fin, Ev), phases and state St, its start and its end predicates
#
# run: one run of the harness (one user turn) as a state machine, after
# LAWS.bend H4. Its live phases: prepare (the request is built; a
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
# noted reply spends a note. The Rust code counts them up; the decisions
# Rust calls (at the end) turn its counts into the counts left.
# A row of the same calls with the same results gets a recovery
# (Recoveries, H4.8), so the run has no loop guard.
#
# LAWS.bend (H4) states what must hold; PROOF.bend proves it through
# proof/run/, and the laws of the requests a run sends (H4.7,
# Reqs at the end) through proof/retry/. The Rust side is
# crates/eukhe-durable/src/harness/generation/decide.rs: it calls the
# decisions at the end through the compiled core (bend/ffi_run.bend).

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

# the reply such a message makes (Ended::reply, LAWS.bend H4.7): its
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
