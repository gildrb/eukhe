# ffi_wait_any: the entry of the compiled Bend core for `jobs.wait`
# (bend/wait_any.bend; Rust: eukhe-bend rules/wait_any.rs).
# Grammar: crates/eukhe-bend/WIRE.md.
#
#   request  a question, its tag then its fields:
#            0 poll: named (Bool), the cancel fired (Bool), the cap passed
#              (Bool), the targets (List<Nat>: 0 running, 1 ready, 2 gone)
#            1 step: the session has a wake path (Bool), the job's
#              watchers (Nat), its phase (Nat: 0 live, 1 kept, 2 sent),
#              the event (Nat: 0 watch, 1 unwatch, 2 settles, 3 taken)
#            2 timeout: the asked seconds (Maybe<Nat>: 0 | 1, the seconds)
#   reply    poll: 0 wait | 1, the index taken | 2 nothing to wait for |
#            3 capped | 4 cancelled; step: the watchers, the phase, the
#            deliveries made (Nat each); timeout: the seconds (Nat)
#
# Malformed input, or input left after the request, answers
# `E wait_any: malformed request`, never a default.
# Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./wait_any.bend as M

# A request of the entry
type Req is Data:
  QPoll{named: Bool, cancel: Bool, late: Bool, ts: List<&2, M.Tgt>}
  QStep{wake: Bool, d: M.D, e: M.Ev}
  QTimeout{asked: Maybe<&2, Nat>}

# Codes
# -----

def tgt_of(n: Nat) -> Maybe<&2, M.Tgt>:
  match n:
    case 0n:
      Some{M.Runs{}}
    case 1n:
      Some{M.Unread{}}
    case 2n:
      Some{M.Read{}}
    case 3n+k:
      None{}

def tgts.cons(t: Maybe<&2, M.Tgt>, r: Maybe<&2, List<&2, M.Tgt>>) -> Maybe<&2, List<&2, M.Tgt>>:
  match t:
    case Some{x}:
      match r:
        case Some{xs}:
          Some{x <> xs}
        case None{}:
          None{}
    case None{}:
      None{}

# the targets the codes ns name, when each is a target's code
def tgts(ns: List<&2, Nat>) -> Maybe<&2, List<&2, M.Tgt>>:
  match ns:
    case Nil{}:
      Some{Nil{}}
    case Con{n, rest}:
      tgts.cons(tgt_of(n), tgts(rest))

def phase_of(n: Nat) -> Maybe<&2, M.Phase>:
  match n:
    case 0n:
      Some{M.Live{}}
    case 1n:
      Some{M.Kept{}}
    case 2n:
      Some{M.Sent{}}
    case 3n+k:
      None{}

def ev_of(n: Nat) -> Maybe<&2, M.Ev>:
  match n:
    case 0n:
      Some{M.Watch{}}
    case 1n:
      Some{M.Unwatch{}}
    case 2n:
      Some{M.Settles{}}
    case 3n:
      Some{M.Taken{}}
    case 4n+k:
      None{}

def phase_code(p: M.Phase) -> Nat:
  match p:
    case M.Live{}:
      0n
    case M.Kept{}:
      1n
    case M.Sent{}:
      2n

# Requests
# --------

def get_poll.ok(n: Bool, c: Bool, l: Bool, ts: Maybe<&2, List<&2, M.Tgt>>, s: String) -> W.Dec<Req>:
  match ts:
    case Some{xs}:
      W.Got{QPoll{n, c, l, xs}, s}
    case None{}:
      W.Bad{}

def get_poll.ts(n: Bool, c: Bool, l: Bool, x: W.Dec<List<&2, Nat>>) -> W.Dec<Req>:
  match x:
    case W.Got{ns, s}:
      get_poll.ok(n, c, l, tgts(ns), s)
    case W.Bad{}:
      W.Bad{}

def get_poll.late(n: Bool, c: Bool, x: W.Dec<Bool>) -> W.Dec<Req>:
  match x:
    case W.Got{l, s}:
      get_poll.ts(n, c, l, W.get_list(~Nat, ~W.get_nat, s))
    case W.Bad{}:
      W.Bad{}

def get_poll.cancel(n: Bool, x: W.Dec<Bool>) -> W.Dec<Req>:
  match x:
    case W.Got{c, s}:
      get_poll.late(n, c, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_poll(x: W.Dec<Bool>) -> W.Dec<Req>:
  match x:
    case W.Got{n, s}:
      get_poll.cancel(n, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_step.ok(k: Bool, w: Nat, p: Maybe<&2, M.Phase>, e: Maybe<&2, M.Ev>, s: String) -> W.Dec<Req>:
  match p:
    case Some{ph}:
      match e:
        case Some{ev}:
          W.Got{QStep{k, M.D{w, ph}, ev}, s}
        case None{}:
          W.Bad{}
    case None{}:
      W.Bad{}

def get_step.ev(k: Bool, w: Nat, p: Nat, x: W.Dec<Nat>) -> W.Dec<Req>:
  match x:
    case W.Got{e, s}:
      get_step.ok(k, w, phase_of(p), ev_of(e), s)
    case W.Bad{}:
      W.Bad{}

def get_step.phase(k: Bool, w: Nat, x: W.Dec<Nat>) -> W.Dec<Req>:
  match x:
    case W.Got{p, s}:
      get_step.ev(k, w, p, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_step.watchers(k: Bool, x: W.Dec<Nat>) -> W.Dec<Req>:
  match x:
    case W.Got{w, s}:
      get_step.phase(k, w, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_step(x: W.Dec<Bool>) -> W.Dec<Req>:
  match x:
    case W.Got{k, s}:
      get_step.watchers(k, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_timeout.ms(x: W.Dec<Nat>) -> W.Dec<Req>:
  match x:
    case W.Got{t, s}:
      W.Got{QTimeout{Some{t}}, s}
    case W.Bad{}:
      W.Bad{}

def get_timeout.tag(t: Nat, s: String) -> W.Dec<Req>:
  match t:
    case 0n:
      W.Got{QTimeout{None{}}, s}
    case 1n:
      get_timeout.ms(W.get_nat(s))
    case 2n+k:
      W.Bad{}

def get_timeout(x: W.Dec<Nat>) -> W.Dec<Req>:
  match x:
    case W.Got{t, s}:
      get_timeout.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_req.tag(t: Nat, s: String) -> W.Dec<Req>:
  match t:
    case 0n:
      get_poll(W.get_bool(s))
    case 1n:
      get_step(W.get_bool(s))
    case 2n:
      get_timeout(W.get_nat(s))
    case 3n+k:
      W.Bad{}

def get_req.start(x: W.Dec<Nat>) -> W.Dec<Req>:
  match x:
    case W.Got{t, s}:
      get_req.tag(t, s)
    case W.Bad{}:
      W.Bad{}

# the request at the start of s
def get_req(s: String) -> W.Dec<Req>:
  get_req.start(W.get_nat(s))

# Replies
# -------

def put_pick(p: M.Pick) -> String:
  match p:
    case M.Waits{}:
      W.put_nat(0n, "")
    case M.Takes{i}:
      W.put_nat(1n, W.put_nat(i, ""))
    case M.NoWork{}:
      W.put_nat(2n, "")
    case M.Capped{}:
      W.put_nat(3n, "")
    case M.Stopped{}:
      W.put_nat(4n, "")

def put_step(r: M.Out) -> String:
  match r:
    case M.Out{d, k}:
      match d:
        case M.D{w, p}:
          W.put_nat(w, W.put_nat(phase_code(p), W.put_nat(k, "")))

# the reply of a request: the model's decision, encoded
def answer(q: Req) -> String:
  match q:
    case QPoll{n, c, l, ts}:
      put_pick(M.poll(n, c, l, ts))
    case QStep{k, d, e}:
      put_step(M.step(k, d, e))
    case QTimeout{a}:
      W.put_nat(M.timeout(a), "")

def ffi.done(q: Req, end: Bool) -> String:
  match end:
    case True{}:
      answer(q)
    case False{}:
      W.err("wait_any: malformed request")

def ffi.got(x: W.Dec<Req>) -> String:
  match x:
    case W.Got{q, +s}:
      ffi.done(q, W.end(s))
    case W.Bad{}:
      W.err("wait_any: malformed request")

# the entry: decode the request, answer the model's decision
def ffi(input: String) -> String:
  ffi.got(get_req(input))
