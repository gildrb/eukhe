# ffi_family: the entry of the compiled Bend core for subagent admission
# (bend/family.bend; Rust: eukhe-bend rules/family.rs).
# Grammar: crates/eukhe-bend/WIRE.md.
#
#   request  the caller's depth, the recursion bound, the family's running
#            subagents, the cap (0: none) (Nat each), the whys of the batch
#            (List<String>; a missing why is "")
#   reply    0, the child's depth (Nat) | 1, the refusal's text (String)
#
# Malformed input, or input left after the request, answers
# `E family: malformed request`, never a default.
# Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./family.bend as F

# A request of the entry
type Req is Data:
  Req{depth: Nat, max: Nat, running: Nat, cap: Nat, whys: List<&2, String>}

# Requests
# --------

def get_req.whys(d: Nat, m: Nat, r: Nat, c: Nat, x: W.Dec<List<&2, String>>) -> W.Dec<Req>:
  match x:
    case W.Got{ws, s}:
      W.Got{Req{d, m, r, c, ws}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.cap(d: Nat, m: Nat, r: Nat, x: W.Dec<Nat>) -> W.Dec<Req>:
  match x:
    case W.Got{c, s}:
      get_req.whys(d, m, r, c, W.get_list(~String, ~W.get_str, s))
    case W.Bad{}:
      W.Bad{}

def get_req.running(d: Nat, m: Nat, x: W.Dec<Nat>) -> W.Dec<Req>:
  match x:
    case W.Got{r, s}:
      get_req.cap(d, m, r, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_req.max(d: Nat, x: W.Dec<Nat>) -> W.Dec<Req>:
  match x:
    case W.Got{m, s}:
      get_req.running(d, m, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_req.depth(x: W.Dec<Nat>) -> W.Dec<Req>:
  match x:
    case W.Got{d, s}:
      get_req.max(d, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

# the request at the start of s
def get_req(s: String) -> W.Dec<Req>:
  get_req.depth(W.get_nat(s))

# The entry
# ---------

def put_verdict(+d: Nat, +m: Nat, v: F.Verdict) -> String:
  match v:
    case F.Admit{k}:
      W.put_nat(0n, W.put_nat(k, ""))
    case F.Refuse{f}:
      W.put_nat(1n, W.put_str(F.text(d, m, f), ""))

# the reply of a request: the model's decision, encoded
def answer(q: Req) -> String:
  match q:
    case Req{+d, +m, r, c, ws}:
      put_verdict(d, m, F.decide(d, m, r, c, ws))

def ffi.done(q: Req, end: Bool) -> String:
  match end:
    case True{}:
      answer(q)
    case False{}:
      W.err("family: malformed request")

def ffi.got(x: W.Dec<Req>) -> String:
  match x:
    case W.Got{q, +s}:
      ffi.done(q, W.end(s))
    case W.Bad{}:
      W.err("family: malformed request")

# the entry: decode the request, answer the model's decision
def ffi(input: String) -> String:
  ffi.got(get_req(input))
