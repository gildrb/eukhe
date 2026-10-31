# ffi_rlm_query: the entry of the compiled Bend core for rlm.query
# (bend/rlm_query.bend; Rust: eukhe-bend rules/rlm_query.rs).
# Grammar: crates/eukhe-bend/WIRE.md.
#
#   request  a question, its tag then its fields:
#            0 plan: the session's query calls running, the cap, the
#              caller's width (0: as wide as allowed), the budget (0:
#              none), the bytes already spent (Nat each), then the input
#              bytes of each call of the batch (List<Nat>)
#            1 cut: the limit in UTF-8 bytes (Nat), then the text (String)
#   reply    plan: 0, the waves (List<Nat>) | 1, the refusal's text
#            (String); cut: 0 (fits) | 1, the bytes kept (Nat)
#
# Malformed input, or input left after the request, answers
# `E rlm_query: malformed request`, never a default.
# Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./rlm_query.bend as Rq

# A request of the entry
type Req is Data:
  QPlan{running: Nat, cap: Nat, width: Nat, budget: Nat, used: Nat, sizes: List<&2, Nat>}
  QCut{max: Nat, text: String}

# Requests
# --------

def get_plan.sizes(r: Nat, c: Nat, w: Nat, b: Nat, u: Nat, x: W.Dec<List<&2, Nat>>) -> W.Dec<Req>:
  match x:
    case W.Got{ss, s}:
      W.Got{QPlan{r, c, w, b, u, ss}, s}
    case W.Bad{}:
      W.Bad{}

def get_plan.used(r: Nat, c: Nat, w: Nat, b: Nat, x: W.Dec<Nat>) -> W.Dec<Req>:
  match x:
    case W.Got{u, s}:
      get_plan.sizes(r, c, w, b, u, W.get_list(~Nat, ~W.get_nat, s))
    case W.Bad{}:
      W.Bad{}

def get_plan.budget(r: Nat, c: Nat, w: Nat, x: W.Dec<Nat>) -> W.Dec<Req>:
  match x:
    case W.Got{b, s}:
      get_plan.used(r, c, w, b, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_plan.width(r: Nat, c: Nat, x: W.Dec<Nat>) -> W.Dec<Req>:
  match x:
    case W.Got{w, s}:
      get_plan.budget(r, c, w, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_plan.cap(r: Nat, x: W.Dec<Nat>) -> W.Dec<Req>:
  match x:
    case W.Got{c, s}:
      get_plan.width(r, c, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_plan(x: W.Dec<Nat>) -> W.Dec<Req>:
  match x:
    case W.Got{r, s}:
      get_plan.cap(r, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_cut.text(m: Nat, x: W.Dec<String>) -> W.Dec<Req>:
  match x:
    case W.Got{t, s}:
      W.Got{QCut{m, t}, s}
    case W.Bad{}:
      W.Bad{}

def get_cut(x: W.Dec<Nat>) -> W.Dec<Req>:
  match x:
    case W.Got{m, s}:
      get_cut.text(m, W.get_str(s))
    case W.Bad{}:
      W.Bad{}

def get_req.tag(t: Nat, s: String) -> W.Dec<Req>:
  match t:
    case 0n:
      get_plan(W.get_nat(s))
    case 1n:
      get_cut(W.get_nat(s))
    case 2n+k:
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

def put_plan(p: Rq.Plan) -> String:
  match p:
    case Rq.Waves{ws}:
      W.put_nat(0n, W.put_list(~Nat, ~W.put_nat, ws, ""))
    case Rq.Refused{f}:
      W.put_nat(1n, W.put_str(Rq.text(f), ""))

def put_trim(x: Rq.Trim) -> String:
  match x:
    case Rq.Fits{}:
      W.put_nat(0n, "")
    case Rq.CutAt{k}:
      W.put_nat(1n, W.put_nat(k, ""))

# the reply of a request: the model's decision, encoded
def answer(q: Req) -> String:
  match q:
    case QPlan{r, c, w, b, u, ss}:
      put_plan(Rq.plan(r, c, w, b, u, ss))
    case QCut{m, t}:
      put_trim(Rq.cut(m, t))

def ffi.done(q: Req, end: Bool) -> String:
  match end:
    case True{}:
      answer(q)
    case False{}:
      W.err("rlm_query: malformed request")

def ffi.got(x: W.Dec<Req>) -> String:
  match x:
    case W.Got{q, +s}:
      ffi.done(q, W.end(s))
    case W.Bad{}:
      W.err("rlm_query: malformed request")

# the entry: decode the request, answer the model's decision
def ffi(input: String) -> String:
  ffi.got(get_req(input))
