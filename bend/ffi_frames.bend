# ffi_frames: the gate of one host-request frame of a kernel's stream
# (bend/sandbox.bend `admit`) as an entry of the compiled Bend core
# (crates/eukhe-core/src/kernel/manager/frames.rs `Gate::admit`, through
# crates/eukhe-bend/src/rules/frames.rs). Rust cuts the stream into frames
# and reads each host request's facts; the core decides. The request
# (crates/eukhe-bend/WIRE.md is the grammar):
#
#   the limit (Nat), whether the frame's id is fresh (Bool), the frame's
#   length (Nat; past the limit, any length past it), its type: 0 (none)
#   | 1, Bool (a type, and whether the host serves it)
#   -> 0 serve | 1 a repeated id | 2 past the limit | 3 no type | 4 a type
#      the host does not serve
#
# Every input that is not exactly one request answers the error form
# "frames: malformed request", never a default. laws/sandbox.bend (section
# frames entry) states this file's laws; PROOF.bend proves them. Pure: no
# IO, no @unsafe.

import Base
import ./wire.bend as W
import ./sandbox.bend as Sb

# A request of the entry
type Req is Data:
  Req{max: Nat, fresh: Bool, len: Nat, kind: Sb.Typed}

# Requests
# --------

def get_named(r: W.Dec<Bool>) -> W.Dec<Sb.Typed>:
  match r:
    case W.Got{b, s}:
      W.Got{Sb.Named{b}, s}
    case W.Bad{}:
      W.Bad{}

def get_kind.tag(t: Nat, s: String) -> W.Dec<Sb.Typed>:
  match t:
    case 0n:
      W.Got{Sb.Unnamed{}, s}
    case 1n:
      get_named(W.get_bool(s))
    case 2n+u:
      W.Bad{}

def get_kind(r: W.Dec<Nat>) -> W.Dec<Sb.Typed>:
  match r:
    case W.Got{t, s}:
      get_kind.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_req.kind(m: Nat, f: Bool, l: Nat, r: W.Dec<Sb.Typed>) -> W.Dec<Req>:
  match r:
    case W.Got{k, s}:
      W.Got{Req{m, f, l, k}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.len(m: Nat, f: Bool, r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{l, s}:
      get_req.kind(m, f, l, get_kind(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_req.fresh(m: Nat, r: W.Dec<Bool>) -> W.Dec<Req>:
  match r:
    case W.Got{f, s}:
      get_req.len(m, f, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_req.max(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{m, s}:
      get_req.fresh(m, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_req(s: String) -> W.Dec<Req>:
  get_req.max(W.get_nat(s))

# Replies
# -------

def put_verdict(v: Sb.Verdict, rest: String) -> String:
  match v:
    case Sb.Serve{}:
      W.put_nat(0n, rest)
    case Sb.Duplicate{}:
      W.put_nat(1n, rest)
    case Sb.Oversize{}:
      W.put_nat(2n, rest)
    case Sb.Kindless{}:
      W.put_nat(3n, rest)
    case Sb.NotServed{}:
      W.put_nat(4n, rest)

# the model's decision on a request, encoded
def answer(q: Req) -> String:
  match q:
    case Req{m, f, l, k}:
      put_verdict(Sb.admit(m, f, l, k), "")

def malformed() -> String:
  W.err("frames: malformed request")

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
