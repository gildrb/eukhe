# ffi_retry: the retry decisions of the compiled Bend core (bend/retry.bend)
# behind one entry, `ffi`. A request names its decision and carries its
# input (crates/eukhe-bend/WIRE.md is the grammar):
#
#   tag 0  classify   the facts of a failure        -> Bool (retry it)
#   tag 1  wait       base, attempt, cap, draw,
#                     the server's wait (Maybe)     -> a Delay
#   tag 2  failover   len, the tried attempts,
#                     the policy                    -> Maybe<Switch>
#   tag 3  stall      the idle deadline it stalled  -> Nat (the next one)
#
# A Cause is its tag in declaration order (Refusal 0 .. Unknown 13); Facts,
# Tried, Policy and Switch are records; a Delay is After (tag 0, ms) or
# Refused (tag 1, server, cap). Malformed input answers the wire's error
# form, never a default. LAWS.bend section retry states the laws of this
# codec; PROOF.bend proves them. Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./retry.bend as R

# A request of the entry
type Req is Data:
  QClassify{facts: R.Facts}
  QWait{base: Nat, attempt: Nat, cap: Nat, draw: Nat, server: Maybe<&2, Nat>}
  QFailover{len: Nat, tried: List<&2, R.Tried>, policy: R.Policy}
  QStall{idle: Nat}

# Maybe<Nat>
# ----------

def put_mnat(m: Maybe<&2, Nat>, rest: String) -> String:
  match m:
    case None{}:
      W.put_nat(0n, rest)
    case Some{n}:
      W.put_nat(1n, W.put_nat(n, rest))

def get_mnat.some(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, Nat>>:
  match r:
    case W.Got{n, s}:
      W.Got{Some{n}, s}
    case W.Bad{}:
      W.Bad{}

def get_mnat.tag(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, Nat>>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          W.Got{None{}, s}
        case 1n:
          get_mnat.some(W.get_nat(s))
        case 2n+k:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_mnat(s: String) -> W.Dec<Maybe<&2, Nat>>:
  get_mnat.tag(W.get_nat(s))

# Cause: its tag
# --------------

def cause.tag(k: R.Cause) -> Nat:
  match k:
    case R.Refusal{}:
      0n
    case R.Safety{}:
      1n
    case R.PaymentRequired{}:
      2n
    case R.Overloaded{}:
      3n
    case R.RateLimit{}:
      4n
    case R.ServerError{}:
      5n
    case R.Auth{}:
      6n
    case R.Permission{}:
      7n
    case R.InvalidRequest{}:
      8n
    case R.MalformedResponse{}:
      9n
    case R.StreamDrop{}:
      10n
    case R.StreamStalled{}:
      11n
    case R.StreamRepeating{}:
      12n
    case R.Unknown{}:
      13n

# the cause of a tag, from Refusal (0) on
def cause.of(t: Nat) -> Maybe<&2, R.Cause>:
  match t:
    case 0n:
      Some{R.Refusal{}}
    case 1n:
      Some{R.Safety{}}
    case 2n:
      Some{R.PaymentRequired{}}
    case 3n:
      Some{R.Overloaded{}}
    case 4n:
      Some{R.RateLimit{}}
    case 5n:
      Some{R.ServerError{}}
    case 6n:
      Some{R.Auth{}}
    case 7n:
      Some{R.Permission{}}
    case 8n:
      Some{R.InvalidRequest{}}
    case 9n:
      Some{R.MalformedResponse{}}
    case 10n:
      Some{R.StreamDrop{}}
    case 11n:
      Some{R.StreamStalled{}}
    case 12n:
      Some{R.StreamRepeating{}}
    case 13n:
      Some{R.Unknown{}}
    case 14n+u:
      None{}

def put_mcause(m: Maybe<&2, R.Cause>, rest: String) -> String:
  match m:
    case None{}:
      W.put_nat(0n, rest)
    case Some{k}:
      W.put_nat(1n, W.put_nat(cause.tag(k), rest))

def get_mcause.known(m: Maybe<&2, R.Cause>, s: String) -> W.Dec<Maybe<&2, R.Cause>>:
  match m:
    case Some{k}:
      W.Got{Some{k}, s}
    case None{}:
      W.Bad{}

def get_mcause.some(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, R.Cause>>:
  match r:
    case W.Got{t, s}:
      get_mcause.known(cause.of(t), s)
    case W.Bad{}:
      W.Bad{}

def get_mcause.tag(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, R.Cause>>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          W.Got{None{}, s}
        case 1n:
          get_mcause.some(W.get_nat(s))
        case 2n+k:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_mcause(s: String) -> W.Dec<Maybe<&2, R.Cause>>:
  get_mcause.tag(W.get_nat(s))

# Facts: parked, limit, status, kind, text
# ----------------------------------------

def put_facts(f: R.Facts, rest: String) -> String:
  match f:
    case R.Facts{parked, limit, status, kind, text}:
      W.put_bool(parked, W.put_bool(limit, put_mnat(status, put_mcause(kind, W.put_bool(text, rest)))))

def get_facts.text(parked: Bool, limit: Bool, status: Maybe<&2, Nat>, kind: Maybe<&2, R.Cause>, r: W.Dec<Bool>) -> W.Dec<R.Facts>:
  match r:
    case W.Got{text, s}:
      W.Got{R.Facts{parked, limit, status, kind, text}, s}
    case W.Bad{}:
      W.Bad{}

def get_facts.kind(parked: Bool, limit: Bool, status: Maybe<&2, Nat>, r: W.Dec<Maybe<&2, R.Cause>>) -> W.Dec<R.Facts>:
  match r:
    case W.Got{kind, s}:
      get_facts.text(parked, limit, status, kind, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_facts.status(parked: Bool, limit: Bool, r: W.Dec<Maybe<&2, Nat>>) -> W.Dec<R.Facts>:
  match r:
    case W.Got{status, s}:
      get_facts.kind(parked, limit, status, get_mcause(s))
    case W.Bad{}:
      W.Bad{}

def get_facts.limit(parked: Bool, r: W.Dec<Bool>) -> W.Dec<R.Facts>:
  match r:
    case W.Got{limit, s}:
      get_facts.status(parked, limit, get_mnat(s))
    case W.Bad{}:
      W.Bad{}

def get_facts.parked(r: W.Dec<Bool>) -> W.Dec<R.Facts>:
  match r:
    case W.Got{parked, s}:
      get_facts.limit(parked, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_facts(s: String) -> W.Dec<R.Facts>:
  get_facts.parked(W.get_bool(s))

# Tried: at, wait
# ---------------

def put_tried(t: R.Tried, rest: String) -> String:
  match t:
    case R.Tried{at, wait}:
      W.put_nat(at, put_mnat(wait, rest))

def get_tried.wait(at: Nat, r: W.Dec<Maybe<&2, Nat>>) -> W.Dec<R.Tried>:
  match r:
    case W.Got{wait, s}:
      W.Got{R.Tried{at, wait}, s}
    case W.Bad{}:
      W.Bad{}

def get_tried.at(r: W.Dec<Nat>) -> W.Dec<R.Tried>:
  match r:
    case W.Got{at, s}:
      get_tried.wait(at, get_mnat(s))
    case W.Bad{}:
      W.Bad{}

def get_tried(s: String) -> W.Dec<R.Tried>:
  get_tried.at(W.get_nat(s))

# Policy: switches, base, max
# ---------------------------

def put_policy(p: R.Policy, rest: String) -> String:
  match p:
    case R.Policy{switches, base, max}:
      W.put_nat(switches, W.put_nat(base, W.put_nat(max, rest)))

def get_policy.max(switches: Nat, base: Nat, r: W.Dec<Nat>) -> W.Dec<R.Policy>:
  match r:
    case W.Got{max, s}:
      W.Got{R.Policy{switches, base, max}, s}
    case W.Bad{}:
      W.Bad{}

def get_policy.base(switches: Nat, r: W.Dec<Nat>) -> W.Dec<R.Policy>:
  match r:
    case W.Got{base, s}:
      get_policy.max(switches, base, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_policy.switches(r: W.Dec<Nat>) -> W.Dec<R.Policy>:
  match r:
    case W.Got{switches, s}:
      get_policy.base(switches, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_policy(s: String) -> W.Dec<R.Policy>:
  get_policy.switches(W.get_nat(s))

# Requests
# --------

def put_req(q: Req, rest: String) -> String:
  match q:
    case QClassify{f}:
      W.put_nat(0n, put_facts(f, rest))
    case QWait{base, attempt, cap, draw, server}:
      W.put_nat(1n, W.put_nat(base, W.put_nat(attempt, W.put_nat(cap, W.put_nat(draw, put_mnat(server, rest))))))
    case QFailover{len, tried, policy}:
      W.put_nat(2n, W.put_nat(len, W.put_list(~R.Tried, ~put_tried, tried, put_policy(policy, rest))))
    case QStall{idle}:
      W.put_nat(3n, W.put_nat(idle, rest))

def get_classify(r: W.Dec<R.Facts>) -> W.Dec<Req>:
  match r:
    case W.Got{f, s}:
      W.Got{QClassify{f}, s}
    case W.Bad{}:
      W.Bad{}

def get_wait.server(base: Nat, attempt: Nat, cap: Nat, draw: Nat, r: W.Dec<Maybe<&2, Nat>>) -> W.Dec<Req>:
  match r:
    case W.Got{server, s}:
      W.Got{QWait{base, attempt, cap, draw, server}, s}
    case W.Bad{}:
      W.Bad{}

def get_wait.draw(base: Nat, attempt: Nat, cap: Nat, r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{draw, s}:
      get_wait.server(base, attempt, cap, draw, get_mnat(s))
    case W.Bad{}:
      W.Bad{}

def get_wait.cap(base: Nat, attempt: Nat, r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{cap, s}:
      get_wait.draw(base, attempt, cap, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_wait.attempt(base: Nat, r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{attempt, s}:
      get_wait.cap(base, attempt, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_wait(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{base, s}:
      get_wait.attempt(base, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_failover.policy(len: Nat, tried: List<&2, R.Tried>, r: W.Dec<R.Policy>) -> W.Dec<Req>:
  match r:
    case W.Got{policy, s}:
      W.Got{QFailover{len, tried, policy}, s}
    case W.Bad{}:
      W.Bad{}

def get_failover.tried(len: Nat, r: W.Dec<List<&2, R.Tried>>) -> W.Dec<Req>:
  match r:
    case W.Got{tried, s}:
      get_failover.policy(len, tried, get_policy(s))
    case W.Bad{}:
      W.Bad{}

def get_failover(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{len, s}:
      get_failover.tried(len, W.get_list(~R.Tried, ~get_tried, s))
    case W.Bad{}:
      W.Bad{}

def get_stall(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{idle, s}:
      W.Got{QStall{idle}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.tag(t: Nat, s: String) -> W.Dec<Req>:
  match t:
    case 0n:
      get_classify(get_facts(s))
    case 1n:
      get_wait(W.get_nat(s))
    case 2n:
      get_failover(W.get_nat(s))
    case 3n:
      get_stall(W.get_nat(s))
    case 4n+u:
      W.Bad{}

def get_req.start(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{t, s}:
      get_req.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_req(s: String) -> W.Dec<Req>:
  get_req.start(W.get_nat(s))

# Replies
# -------

def put_delay(d: R.Delay, rest: String) -> String:
  match d:
    case R.After{ms}:
      W.put_nat(0n, W.put_nat(ms, rest))
    case R.Refused{server, cap}:
      W.put_nat(1n, W.put_nat(server, W.put_nat(cap, rest)))

def put_switch(m: Maybe<&2, R.Switch>, rest: String) -> String:
  match m:
    case None{}:
      W.put_nat(0n, rest)
    case Some{sw}:
      match sw:
        case R.Switch{to, delay}:
          W.put_nat(1n, W.put_nat(to, W.put_nat(delay, rest)))

# the reply of a request: the model's decision, encoded
def answer(q: Req) -> String:
  match q:
    case QClassify{f}:
      W.put_bool(R.retryable(f), "")
    case QWait{base, attempt, cap, draw, server}:
      put_delay(R.retry_wait(base, attempt, cap, draw, server), "")
    case QFailover{len, tried, policy}:
      put_switch(R.next(len, tried, policy), "")
    case QStall{idle}:
      W.put_nat(R.stall.next(idle), "")

def ffi.done(q: Req, end: Bool) -> String:
  match end:
    case True{}:
      answer(q)
    case False{}:
      W.err("retry: input left after the request")

def ffi.got(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, +s}:
      ffi.done(q, W.end(s))
    case W.Bad{}:
      W.err("retry: malformed request")

# the entry: decode the request, answer the model's decision
def ffi(input: String) -> String:
  ffi.got(get_req(input))
