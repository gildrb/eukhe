# ffi_approvals: where a question of the approval gate goes, one session
# at a time (bend/approvals.bend `next`, `answered`, `default_auto`), as an
# entry of the compiled Bend core (crates/eukhe-daemon/src/shell_approval.rs
# through crates/eukhe-bend/src/rules/approvals.rs). The interleaving of the
# sessions (a relay over the supervisor, clients that leave, the first
# answer) stays in Rust; each session's decision is this entry's. A request
# names its question (crates/eukhe-bend/WIRE.md is the grammar):
#
#   tag 0  next      who answers the session now (0 nobody, 1 the phone
#                    gateway alone, 2 an interactive client), the step's
#                    effects (List<Nat>), whether the session has a parent
#                    (Bool)
#                    -> 0 (show the question to its clients) | 1 (relay it
#                       to the parent) | 2, fate (it ends here: 0 runs,
#                       1 denied, 2 unanswered, 3 refused by the gateway
#                       rule)
#   tag 1  answered  the step's effects, the clients' answer (Bool)
#                    -> the fate
#   tag 2  default   (nothing)
#                    -> the default auto set (List<Nat>)
#
# Every input that is not exactly one request answers the error form
# "approvals: malformed request", never a default. laws/approvals.bend
# (section approvals entry) states this file's laws; PROOF.bend proves
# them. Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./approvals.bend as Am

# A request of the entry
type Req is Data:
  QNext{here: Am.Here, effs: List<&2, Nat>, parent: Bool}
  QAnswered{effs: List<&2, Nat>, yes: Bool}
  QDefault{}

# Requests
# --------

def get_ns(s: String) -> W.Dec<List<&2, Nat>>:
  W.get_list(~Nat, ~W.get_nat, s)

def get_next.parent(h: Am.Here, es: List<&2, Nat>, r: W.Dec<Bool>) -> W.Dec<Req>:
  match r:
    case W.Got{p, s}:
      W.Got{QNext{h, es, p}, s}
    case W.Bad{}:
      W.Bad{}

def get_next.effs(h: Am.Here, r: W.Dec<List<&2, Nat>>) -> W.Dec<Req>:
  match r:
    case W.Got{es, s}:
      get_next.parent(h, es, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_next.here(t: Nat, s: String) -> W.Dec<Req>:
  match t:
    case 0n:
      get_next.effs(Am.Nobody{}, get_ns(s))
    case 1n:
      get_next.effs(Am.GatewayOnly{}, get_ns(s))
    case 2n:
      get_next.effs(Am.Clients{}, get_ns(s))
    case 3n+u:
      W.Bad{}

def get_next(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{t, s}:
      get_next.here(t, s)
    case W.Bad{}:
      W.Bad{}

def get_answered.yes(es: List<&2, Nat>, r: W.Dec<Bool>) -> W.Dec<Req>:
  match r:
    case W.Got{y, s}:
      W.Got{QAnswered{es, y}, s}
    case W.Bad{}:
      W.Bad{}

def get_answered(r: W.Dec<List<&2, Nat>>) -> W.Dec<Req>:
  match r:
    case W.Got{es, s}:
      get_answered.yes(es, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_req.tag(t: Nat, s: String) -> W.Dec<Req>:
  match t:
    case 0n:
      get_next(W.get_nat(s))
    case 1n:
      get_answered(get_ns(s))
    case 2n:
      W.Got{QDefault{}, s}
    case 3n+u:
      W.Bad{}

def get_req.go(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{t, s}:
      get_req.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_req(s: String) -> W.Dec<Req>:
  get_req.go(W.get_nat(s))

# Replies
# -------

def put_fate(f: Am.Fate, rest: String) -> String:
  match f:
    case Am.Runs{}:
      W.put_nat(0n, rest)
    case Am.Denied{}:
      W.put_nat(1n, rest)
    case Am.Unheard{}:
      W.put_nat(2n, rest)
    case Am.GatewayRefused{}:
      W.put_nat(3n, rest)

def put_next(x: Am.Next, rest: String) -> String:
  match x:
    case Am.Show{}:
      W.put_nat(0n, rest)
    case Am.Relay{}:
      W.put_nat(1n, rest)
    case Am.Ends{f}:
      W.put_nat(2n, put_fate(f, rest))

# the model's decision on a request, encoded
def answer(q: Req) -> String:
  match q:
    case QNext{h, es, p}:
      put_next(Am.next(es, h, p), "")
    case QAnswered{es, y}:
      put_fate(Am.answered(es, y), "")
    case QDefault{}:
      W.put_list(~Nat, ~W.put_nat, Am.default_auto(), "")

def malformed() -> String:
  W.err("approvals: malformed request")

def run.end(whole: Bool, q: Req) -> String:
  match whole:
    case True{}:
      answer(q)
    case False{}:
      malformed()

def run(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, s}:
      run.end(W.end(s), q)
    case W.Bad{}:
      malformed()

# the entry: decode the request, answer the model's decision
def ffi(input: String) -> String:
  run(get_req(input))
