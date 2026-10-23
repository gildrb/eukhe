# run: the requests a run sends (H4.7): Req/Reqs, how each step changes them, cut/fresh and the lines the model reads

import Base
import ./state.bend as RnState
import ./step.bend as RnStep

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
def Reqs.prepared(pa: RnState.Ph, +ctx: Nat, n: Nat, +note: Nat, log: List<&2, Sent>) -> Reqs:
  match pa:
    case RnState.Call{}:
      Reqs{ctx, n, note, Sent{Req{ctx, note}} <> log}
    case RnState.Prepare{}:
      Reqs{ctx, n, note, log}
    case RnState.Compact{over}:
      Reqs{ctx, n, note, log}
    case RnState.Tools{}:
      Reqs{ctx, n, note, log}
    case RnState.Answered{}:
      Reqs{ctx, n, note, log}
    case RnState.Aborted{}:
      Reqs{ctx, n, note, log}
    case RnState.Failed{why}:
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

def Reqs.reply(reply: RnState.Reply, +ctx: Nat, +n: Nat, note: Nat, log: List<&2, Sent>) -> Reqs:
  match reply:
    case RnState.Error{retryable, noted}:
      Reqs.error(noted, ctx, n, note, log)
    case RnState.Plain{}:
      Reqs{ctx, n, note, log}
    case RnState.Calls{}:
      Reqs{ctx, n, note, log}
    case RnState.Deferred{}:
      Reqs{ctx, n, note, log}
    case RnState.Overflow{cut}:
      Reqs{ctx, n, note, log}

# a compaction that appended its entry grows the context
def Reqs.compacted(got: RnState.Got, ctx: Nat, n: Nat, note: Nat, log: List<&2, Sent>) -> Reqs:
  match got:
    case RnState.Built{}:
      Reqs{1n+ctx, n, note, log}
    case RnState.Kept{}:
      Reqs{ctx, n, note, log}
    case RnState.Broke{}:
      Reqs{ctx, n, note, log}

# a round that goes on to the next generation grows the context; that
# generation starts at attempt 1, with no note
def Reqs.rounded(pa: RnState.Ph, ctx: Nat, n: Nat, note: Nat, log: List<&2, Sent>) -> Reqs:
  match pa:
    case RnState.Prepare{}:
      Reqs{1n+ctx, 1n, 0n, log}
    case RnState.Call{}:
      Reqs{ctx, n, note, log}
    case RnState.Compact{over}:
      Reqs{ctx, n, note, log}
    case RnState.Tools{}:
      Reqs{ctx, n, note, log}
    case RnState.Answered{}:
      Reqs{ctx, n, note, log}
    case RnState.Aborted{}:
      Reqs{ctx, n, note, log}
    case RnState.Failed{why}:
      Reqs{ctx, n, note, log}

def Reqs.go(pb: RnState.Ph, e: RnState.Ev, pa: RnState.Ph, +ctx: Nat, +n: Nat, +note: Nat, log: List<&2, Sent>) -> Reqs:
  match pb e:
    case RnState.Prepare{} e:
      Reqs.prepared(pa, ctx, n, note, log)
    case RnState.Call{} RnState.Go{reply, fin, got}:
      Reqs.reply(reply, ctx, n, note, log)
    case RnState.Call{} RnState.Abort{}:
      Reqs{ctx, n, note, log}
    case RnState.Compact{over} RnState.Go{reply, fin, got}:
      Reqs.compacted(got, ctx, n, note, log)
    case RnState.Compact{over} RnState.Abort{}:
      Reqs{ctx, n, note, log}
    case RnState.Tools{} e:
      Reqs.rounded(pa, ctx, n, note, log)
    case RnState.Answered{} e:
      Reqs{ctx, n, note, log}
    case RnState.Aborted{} e:
      Reqs{ctx, n, note, log}
    case RnState.Failed{why} e:
      Reqs{ctx, n, note, log}

# the requests after input e takes the run from phase pb to phase pa
def Reqs.step(pb: RnState.Ph, e: RnState.Ev, pa: RnState.Ph, t: Reqs) -> Reqs:
  match t:
    case Reqs{ctx, n, note, log}:
      Reqs.go(pb, e, pa, ctx, n, note, log)

def reqs.go(evs: List<&2, RnState.Ev>, +cfg: RnState.Cfg, +s: RnState.St, t: Reqs) -> Reqs:
  match evs:
    case Nil{}:
      t
    case +e <> rest:
      +s2 = RnStep.step(cfg, s, e)
      reqs.go(rest, cfg, s2, Reqs.step(RnState.St.ph(s), e, RnState.St.ph(s2), t))

# the requests of the run after evs
def reqs(+cfg: RnState.Cfg, evs: List<&2, RnState.Ev>) -> Reqs:
  reqs.go(evs, cfg, RnState.init(cfg), Reqs.init())

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
