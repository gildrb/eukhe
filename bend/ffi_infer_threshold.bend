import Base
import ./wire.bend as W
import ./infer_threshold.bend as M

# ffi_infer_threshold: which compaction threshold a request's context is
# over and where a compaction cuts (bend/infer_threshold.bend `plan`;
# bend/infer.bend section 5) as an entry of the compiled Bend core. Rust
# (crates/eukhe-durable compaction/range.rs `plan`) counts the tokens,
# sizes the entries and rounds the policy's reserve and margin up to whole
# tokens; the model decides.
# Request (a record): compaction on (Bool), the context's tokens, the
# model's window (0: unknown), the reserve, the margin, keepRecentTokens,
# full, the entries' sizes newest first (a list), the cuts (a list); a
# reserve or a margin is 0 then n (n tokens) | 1 then n (-(1+n) tokens).
# Reply: the threshold 0 none | 1 the background threshold | 2 the
# blocking threshold, then the cut 0 none | 1 then how many entries it
# keeps. Any other input: the error form.

# A request of the entry
type Req is Data:
  Req{on: Bool, t: Nat, w: Nat, r: M.Z, m: M.Z, keep: Nat, full: Nat, xs: List<&2, Nat>, cuts: List<&2, Nat>}

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

def get_req.cuts(on: Bool, t: Nat, w: Nat, r: M.Z, m: M.Z, keep: Nat, full: Nat, xs: List<&2, Nat>, d: W.Dec<List<&2, Nat>>) -> W.Dec<Req>:
  match d:
    case W.Got{cuts, s}:
      W.Got{Req{on, t, w, r, m, keep, full, xs, cuts}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.sizes(on: Bool, t: Nat, w: Nat, r: M.Z, m: M.Z, keep: Nat, full: Nat, d: W.Dec<List<&2, Nat>>) -> W.Dec<Req>:
  match d:
    case W.Got{xs, s}:
      get_req.cuts(on, t, w, r, m, keep, full, xs, W.get_list(~Nat, ~W.get_nat, s))
    case W.Bad{}:
      W.Bad{}

def get_req.full(on: Bool, t: Nat, w: Nat, r: M.Z, m: M.Z, keep: Nat, d: W.Dec<Nat>) -> W.Dec<Req>:
  match d:
    case W.Got{full, s}:
      get_req.sizes(on, t, w, r, m, keep, full, W.get_list(~Nat, ~W.get_nat, s))
    case W.Bad{}:
      W.Bad{}

def get_req.keep(on: Bool, t: Nat, w: Nat, r: M.Z, m: M.Z, d: W.Dec<Nat>) -> W.Dec<Req>:
  match d:
    case W.Got{keep, s}:
      get_req.full(on, t, w, r, m, keep, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_req.margin(on: Bool, t: Nat, w: Nat, r: M.Z, d: W.Dec<M.Z>) -> W.Dec<Req>:
  match d:
    case W.Got{m, s}:
      get_req.keep(on, t, w, r, m, W.get_nat(s))
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

def put_over(o: M.Over, rest: String) -> String:
  match o:
    case M.Under{}:
      W.put_nat(0n, rest)
    case M.Early{}:
      W.put_nat(1n, rest)
    case M.Blocks{}:
      W.put_nat(2n, rest)

def put_cut(c: Maybe<&2, Nat>) -> String:
  match c:
    case None{}:
      W.put_nat(0n, "")
    case Some{k}:
      W.put_nat(1n, W.put_nat(k, ""))

def put_plan(p: M.Plan) -> String:
  match p:
    case M.Plan{o, c}:
      put_over(o, put_cut(c))

# the answer to a request
def answer(q: Req) -> String:
  match q:
    case Req{on, t, w, r, m, keep, full, xs, cuts}:
      put_plan(M.plan(on, t, w, r, m, keep, full, xs, cuts))

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
