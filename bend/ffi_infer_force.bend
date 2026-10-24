import Base
import ./wire.bend as W
import ./infer_force.bend as M

# ffi_infer_force: the steps of a forced tool call (bend/infer_force.bend
# `flag`, `after`; bend/infer.bend section 2) as an entry of the compiled
# Bend core. Rust (crates/eukhe-durable generation.rs) keeps the count of
# the requests made and sends it; the model decides.
# Request: a tag, then
#   0  the native flag of a request: its attempt (0: the first), whether
#      the provider supports the flag, whether it is free
#   1  after the reply to a request: its attempt, the call's retries,
#      whether the reply called the tool
# Reply to 0: the flag (Bool). Reply to 1: 0 the tool was called | 1 the
# next request goes | 2 the forced call fails. Any other input: the error
# form.

# A request of the entry
type Req is Data:
  QFlag{i: Nat, sup: Bool, free: Bool}
  QAfter{i: Nat, r: Nat, c: Bool}

# Decoding
# --------

def get_flag.free(i: Nat, sup: Bool, d: W.Dec<Bool>) -> W.Dec<Req>:
  match d:
    case W.Got{free, s}:
      W.Got{QFlag{i, sup, free}, s}
    case W.Bad{}:
      W.Bad{}

def get_flag.sup(i: Nat, d: W.Dec<Bool>) -> W.Dec<Req>:
  match d:
    case W.Got{sup, s}:
      get_flag.free(i, sup, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_flag(d: W.Dec<Nat>) -> W.Dec<Req>:
  match d:
    case W.Got{i, s}:
      get_flag.sup(i, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_after.called(i: Nat, r: Nat, d: W.Dec<Bool>) -> W.Dec<Req>:
  match d:
    case W.Got{c, s}:
      W.Got{QAfter{i, r, c}, s}
    case W.Bad{}:
      W.Bad{}

def get_after.retries(i: Nat, d: W.Dec<Nat>) -> W.Dec<Req>:
  match d:
    case W.Got{r, s}:
      get_after.called(i, r, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_after(d: W.Dec<Nat>) -> W.Dec<Req>:
  match d:
    case W.Got{i, s}:
      get_after.retries(i, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_req.tag(t: Nat, s: String) -> W.Dec<Req>:
  match t:
    case 0n:
      get_flag(W.get_nat(s))
    case 1n:
      get_after(W.get_nat(s))
    case 2n+p:
      W.Bad{}

def get_req.go(d: W.Dec<Nat>) -> W.Dec<Req>:
  match d:
    case W.Got{t, s}:
      get_req.tag(t, s)
    case W.Bad{}:
      W.Bad{}

# the request at the start of s
def get_req(s: String) -> W.Dec<Req>:
  get_req.go(W.get_nat(s))

# Encoding
# --------

def put_next(n: M.Next) -> String:
  match n:
    case M.Hit{}:
      W.put_nat(0n, "")
    case M.Again{}:
      W.put_nat(1n, "")
    case M.Fails{}:
      W.put_nat(2n, "")

# the answer to a request
def answer(q: Req) -> String:
  match q:
    case QFlag{i, sup, free}:
      W.put_bool(M.flag(i, sup, free), "")
    case QAfter{i, r, c}:
      put_next(M.after(i, r, c))

def fail() -> String:
  W.err("infer_force: malformed request")

def run.end(whole: Bool, q: Req) -> String:
  match whole:
    case True{}:
      answer(q)
    case False{}:
      fail()

def run(d: W.Dec<Req>) -> String:
  match d:
    case W.Got{q, s}:
      run.end(W.end(s), q)
    case W.Bad{}:
      fail()

def ffi(input: String) -> String:
  run(get_req(input))
