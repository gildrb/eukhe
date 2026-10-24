import Base
import ./wire.bend as W
import ./infer_threshold.bend as M

# ffi_infer_threshold: which compaction threshold a request's context is
# over (bend/infer_threshold.bend `over`; bend/infer.bend section 5) as an
# entry of the compiled Bend core. Rust (crates/eukhe-durable
# generation.rs `threshold_compaction`) counts the tokens and rounds the
# policy's reserve and margin up to whole tokens; the model decides.
# Request (a record): compaction on (Bool), the context's tokens, the
# model's window (0: unknown), the reserve, the margin; a reserve or a
# margin is 0 then n (n tokens) | 1 then n (-(1+n) tokens).
# Reply: 0 none | 1 the background threshold | 2 the blocking threshold.
# Any other input: the error form.

# A request of the entry
type Req is Data:
  Req{on: Bool, t: Nat, w: Nat, r: M.Z, m: M.Z}

# Decoding
# --------

def get_z.up(d: W.Dec<Nat>) -> W.Dec<M.Z>:
  match d:
    case W.Got{n, s}:
      W.Got{M.Up{n}, s}
    case W.Bad{}:
      W.Bad{}

def get_z.down(d: W.Dec<Nat>) -> W.Dec<M.Z>:
  match d:
    case W.Got{n, s}:
      W.Got{M.Down{n}, s}
    case W.Bad{}:
      W.Bad{}

def get_z.tag(t: Nat, s: String) -> W.Dec<M.Z>:
  match t:
    case 0n:
      get_z.up(W.get_nat(s))
    case 1n:
      get_z.down(W.get_nat(s))
    case 2n+p:
      W.Bad{}

def get_z(d: W.Dec<Nat>) -> W.Dec<M.Z>:
  match d:
    case W.Got{t, s}:
      get_z.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_req.margin(on: Bool, t: Nat, w: Nat, r: M.Z, d: W.Dec<M.Z>) -> W.Dec<Req>:
  match d:
    case W.Got{m, s}:
      W.Got{Req{on, t, w, r, m}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.reserve(on: Bool, t: Nat, w: Nat, d: W.Dec<M.Z>) -> W.Dec<Req>:
  match d:
    case W.Got{r, s}:
      get_req.margin(on, t, w, r, get_z(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_req.window(on: Bool, t: Nat, d: W.Dec<Nat>) -> W.Dec<Req>:
  match d:
    case W.Got{w, s}:
      get_req.reserve(on, t, w, get_z(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_req.tokens(on: Bool, d: W.Dec<Nat>) -> W.Dec<Req>:
  match d:
    case W.Got{t, s}:
      get_req.window(on, t, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_req.go(d: W.Dec<Bool>) -> W.Dec<Req>:
  match d:
    case W.Got{on, s}:
      get_req.tokens(on, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

# the request at the start of s
def get_req(s: String) -> W.Dec<Req>:
  get_req.go(W.get_bool(s))

# Encoding
# --------

def put_over(o: M.Over) -> String:
  match o:
    case M.Under{}:
      W.put_nat(0n, "")
    case M.Early{}:
      W.put_nat(1n, "")
    case M.Blocks{}:
      W.put_nat(2n, "")

# the answer to a request
def answer(q: Req) -> String:
  match q:
    case Req{on, t, w, r, m}:
      put_over(M.over(on, t, w, r, m))

def fail() -> String:
  W.err("infer_threshold: malformed request")

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
