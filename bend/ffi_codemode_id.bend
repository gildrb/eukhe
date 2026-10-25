# ffi_codemode_id: the compiled Bend core's entry for the identifiers of
# code mode (bend/codemode_id.bend). Rust `eukhe_bend::rules::codemode_id`
# calls it through `eukhe_bend::call`.
#
# Request (crates/eukhe-bend/WIRE.md): a question, its tag then its text:
#   tag 0  identifier  a tool's name (String) -> its identifier (String)
#   tag 1  test        a text (String) -> whether it is an identifier (Bool)
# A malformed request (an unknown tag, a short text) answers the error form
# "codemode_id: malformed request"; input left after the request answers
# "codemode_id: input left after the request": never a default.
# laws/codemode_id.bend (section entry) states this file's laws. Pure: no
# IO, no @unsafe.

import Base
import ./wire.bend as W
import ./codemode_id.bend as Ci

# A request of the entry
type Req is Data:
  QId{name: String}
  QIs{text: String}

# Requests
# --------

def get_id(r: W.Dec<String>) -> W.Dec<Req>:
  match r:
    case W.Got{n, s}:
      W.Got{QId{n}, s}
    case W.Bad{}:
      W.Bad{}

def get_is(r: W.Dec<String>) -> W.Dec<Req>:
  match r:
    case W.Got{n, s}:
      W.Got{QIs{n}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.tag(t: Nat, s: String) -> W.Dec<Req>:
  match t:
    case 0n:
      get_id(W.get_str(s))
    case 1n:
      get_is(W.get_str(s))
    case 2n+u:
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

# the reply of a request: the model's answer, encoded
def answer(q: Req) -> String:
  match q:
    case QId{n}:
      W.put_str(Ci.of(n), "")
    case QIs{n}:
      W.put_bool(Ci.test(n), "")

def ffi.done(q: Req, end: Bool) -> String:
  match end:
    case True{}:
      answer(q)
    case False{}:
      W.err("codemode_id: input left after the request")

def ffi.got(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, +s}:
      ffi.done(q, W.end(s))
    case W.Bad{}:
      W.err("codemode_id: malformed request")

# the entry: decode the question, answer the model's answer
def ffi(input: String) -> String:
  ffi.got(get_req(input))
