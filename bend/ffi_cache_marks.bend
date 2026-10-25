# ffi_cache_marks: the entry of the compiled Bend core for the cache-mark
# budget of one provider request (bend/cache_marks.bend; Rust: eukhe-bend
# rules/cache_marks.rs). Grammar: crates/eukhe-bend/WIRE.md.
#
#   request  0, marked (Nat)                       the excess question
#            1, placed (Nat), wants (List<Bool>)   the budget question
#   reply    excess: 0 none | 1, the error text (String)
#            budget: one Bool per wanted mark (List<Bool>)
#
# Malformed input, or input left after the request, answers
# `E cache_marks: malformed request`, never a default.
# Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./cache_marks.bend as Cm

# A request of the entry
type Req is Data:
  QExcess{marked: Nat}
  QGrant{placed: Nat, wants: List<&2, Bool>}

def get_req.wants(placed: Nat, r: W.Dec<List<&2, Bool>>) -> W.Dec<Req>:
  match r:
    case W.Got{ws, s}:
      W.Got{QGrant{placed, ws}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.placed(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{n, s}:
      get_req.wants(n, W.get_list(~Bool, ~W.get_bool, s))
    case W.Bad{}:
      W.Bad{}

def get_req.marked(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{n, s}:
      W.Got{QExcess{n}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.tag(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          get_req.marked(W.get_nat(s))
        case 1n:
          get_req.placed(W.get_nat(s))
        case 2n+k:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

# the request at the start of s
def get_req(s: String) -> W.Dec<Req>:
  get_req.tag(W.get_nat(s))

# The entry
# ---------

def put_excess(m: Maybe<&2, String>) -> String:
  match m:
    case None{}:
      W.put_nat(0n, "")
    case Some{e}:
      W.put_nat(1n, W.put_str(e, ""))

# the reply of a request: the model's answer, encoded
def answer(q: Req) -> String:
  match q:
    case QExcess{n}:
      put_excess(Cm.excess(n))
    case QGrant{p, ws}:
      W.put_list(~Bool, ~W.put_bool, Cm.grant(p, ws), "")

def ffi.done(q: Req, end: Bool) -> String:
  match end:
    case True{}:
      answer(q)
    case False{}:
      W.err("cache_marks: malformed request")

def ffi.got(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, +s}:
      ffi.done(q, W.end(s))
    case W.Bad{}:
      W.err("cache_marks: malformed request")

# the entry: decode the request, answer the model's decision
def ffi(input: String) -> String:
  ffi.got(get_req(input))
